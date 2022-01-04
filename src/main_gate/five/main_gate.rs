use crate::main_gate::{CombinationOptionCommon, MainGateInstructions, Term};
use crate::{Assigned, AssignedBit, AssignedCondition, AssignedValue, UnassignedValue};
use halo2::arithmetic::FieldExt;
use halo2::circuit::{Cell, Region};
use halo2::plonk::{Advice, Column, ConstraintSystem, Error, Fixed};
use halo2::poly::Rotation;
use std::marker::PhantomData;

const WIDTH: usize = 5;

pub enum MainGateColumn {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
}

impl MainGateColumn {
    fn index(&self) -> usize {
        match *self {
            MainGateColumn::A => MainGateColumn::A as usize,
            MainGateColumn::B => MainGateColumn::B as usize,
            MainGateColumn::C => MainGateColumn::C as usize,
            MainGateColumn::D => MainGateColumn::D as usize,
            MainGateColumn::E => MainGateColumn::E as usize,
        }
    }
}

pub struct AssignedCells {
    pub a: Cell,
    pub b: Cell,
    pub c: Cell,
    pub d: Cell,
    pub e: Cell,
}

impl AssignedCells {
    fn new(a: Cell, b: Cell, c: Cell, d: Cell, e: Cell) -> Self {
        AssignedCells { a, b, c, d, e }
    }
}

#[derive(Clone, Debug)]
pub struct MainGateConfig {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub d: Column<Advice>,
    pub e: Column<Advice>,

    pub sa: Column<Fixed>,
    pub sb: Column<Fixed>,
    pub sc: Column<Fixed>,
    pub sd: Column<Fixed>,
    pub se: Column<Fixed>,

    pub se_next: Column<Fixed>,

    pub s_mul_ab: Column<Fixed>,
    pub s_mul_cd: Column<Fixed>,

    pub s_constant: Column<Fixed>,
}

pub struct MainGate<F: FieldExt> {
    pub config: MainGateConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub enum CombinationOption<F: FieldExt> {
    Common(CombinationOptionCommon<F>),
    OneLinerDoubleMul,
    CombineToNextDoubleMul(F),
}

impl<F: FieldExt> From<CombinationOptionCommon<F>> for CombinationOption<F> {
    fn from(option: CombinationOptionCommon<F>) -> Self {
        CombinationOption::Common(option)
    }
}

impl<F: FieldExt> MainGateInstructions<F, WIDTH> for MainGate<F> {
    type CombinationOption = CombinationOption<F>;
    type AssignedCells = AssignedCells;
    type MainGateColumn = MainGateColumn;

    fn add(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        self.add_with_constant(region, a, b, F::zero(), offset)
    }

    fn sub(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        self.sub_with_constant(region, a, b, F::zero(), offset)
    }

    fn add_with_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        aux: F,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b.value()) {
            (Some(a), Some(b)) => Some(a + b + aux),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_add(&b),
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            aux,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn add_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        constant: F,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match a.value() {
            Some(a) => Some(a + constant),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::Zero,
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            constant,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn neg_with_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        aux: F,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match a.value() {
            Some(a) => Some(-a + aux),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_sub(&a),
                Term::Zero,
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            aux,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn sub_with_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        aux: F,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b.value()) {
            (Some(a), Some(b)) => Some(a - b + aux),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_sub(&b),
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            aux,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn sub_sub_with_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b_0: impl Assigned<F>,
        b_1: impl Assigned<F>,
        aux: F,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b_0.value(), b_1.value()) {
            (Some(a), Some(b_0), Some(b_1)) => Some(a - b_0 - b_1 + aux),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_sub(&b_0),
                Term::assigned_to_sub(&b_1),
                Term::unassigned_to_sub(c),
                Term::Zero,
            ],
            aux,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.d, c))
    }

    fn mul2(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match a.value() {
            Some(a) => Some(a + a),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_add(&a),
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn mul3(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match a.value() {
            Some(a) => Some(a + a + a),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_add(&a),
                Term::assigned_to_add(&a),
                Term::unassigned_to_sub(c),
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn mul(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b.value()) {
            (Some(a), Some(b)) => Some(a * b),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(&a),
                Term::assigned_to_mul(&b),
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(AssignedValue::new(cells.c, c))
    }

    fn div_unsafe(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b.value()) {
            (Some(a), Some(b)) => match b.invert().into() {
                Some(b_inverted) => Some(a * &b_inverted),
                // Non inversion case will never be verified
                _ => Some(F::zero()),
            },
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(&b),
                Term::unassigned_to_mul(c),
                Term::assigned_to_add(&a),
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(AssignedValue::new(cells.b, c))
    }

    fn div(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(AssignedValue<F>, AssignedCondition<F>), Error> {
        let (b_inverted, cond) = self.invert(region, b, offset)?;
        let res = self.mul(region, a, b_inverted, offset)?;
        Ok((res, cond))
    }

    fn invert_unsafe(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        // Just enforce the equation below
        // If input 'a' is zero then no valid witness will be found
        // a * a' - 1 = 0

        let inverse = match a.value() {
            Some(a) => match a.invert().into() {
                Some(a) => Some(a),
                // Non inversion case will never be verified
                _ => Some(F::zero()),
            },
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(&a),
                Term::unassigned_to_mul(inverse),
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            -F::one(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(AssignedValue::new(cells.b, inverse))
    }

    fn invert(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(AssignedValue<F>, AssignedCondition<F>), Error> {
        let (one, zero) = (F::one(), F::zero());

        // Returns 'r' as a condition bit that defines if inversion successful or not

        // First enfoce 'r' to be a bit
        // (a * a') - 1 + r = 0
        // r * a' - r = 0
        // if r = 1 then a' = 1
        // if r = 0 then a' = 1/a

        // Witness layout:
        // | A | B  | C | D |
        // | - | -- | - | - |
        // | a | a' | r | - |
        // | r | a' | r | - |

        let (r, a_inv) = match a.value() {
            Some(a) => match a.invert().into() {
                Some(e) => (Some(zero), Some(e)),
                None => (Some(one), Some(one)),
            },
            _ => (None, None),
        };

        let r = self.assign_bit(region, &r.into(), offset)?;

        // (a * a') - 1 + r = 0
        // | A | B  | C | D |
        // | - | -- | - | - |
        // | a | a' | r | - |
        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(&a),
                Term::unassigned_to_mul(a_inv),
                Term::assigned_to_add(&r),
                Term::Zero,
                Term::Zero,
            ],
            -one,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;
        let a_inv = AssignedValue::new(cells.b, a_inv);

        // r * a' - r = 0
        // | A | B  | C | D |
        // | - | -- | - | - |
        // | r | a' | r | - |

        self.combine(
            region,
            [
                Term::assigned_to_mul(&r),
                Term::assigned_to_mul(&a_inv),
                Term::assigned_to_sub(&r),
                Term::Zero,
                Term::Zero,
            ],
            zero,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok((a_inv, r))
    }

    fn assert_equal(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_sub(&b),
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(())
    }

    fn assert_not_equal(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        // (a - b) must have an inverse
        let c = self.sub_with_constant(region, a, b, F::zero(), offset)?;
        self.assert_not_zero(region, c, offset)
    }

    fn is_equal(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedCondition<F>, Error> {
        let (one, zero) = (F::one(), F::zero());

        // Given a and b equation below is enforced
        // 0 = (a - b) * (r * (1 - x) + x) + r - 1
        // Where r and x is witnesses and r is enforced to be a bit

        // Witness layout:
        // | A   | B | C | D |
        // | --- | - | - | - |
        // | dif | a | b | - |
        // | r   | x | u | - |
        // | dif | u | r | - |

        let (x, r) = match (a.value(), b.value()) {
            (Some(a), Some(b)) => {
                let c = a - b;
                match c.invert().into() {
                    Some(inverted) => (Some(inverted), Some(zero)),
                    None => (Some(one), Some(one)),
                }
            }
            _ => (None, None),
        };

        let r = self.assign_bit(region, &r.into(), offset)?;
        let dif = self.sub(region, a, b, offset)?;

        // 0 = rx - r - x + u
        // | A   | B | C | D |
        // | --- | - | - | - |
        // | r   | x | u | - |

        let u = match (r.value(), x) {
            (Some(r), Some(x)) => Some(r - r * x + x),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_sub(&r),
                Term::unassigned_to_sub(x),
                Term::unassigned_to_add(u),
                Term::Zero,
                Term::Zero,
            ],
            zero,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        let u = AssignedValue::new(cells.c, u);

        // 0 = u * dif + r - 1
        // | A   | B | C | D |
        // | --- | - | - | - |
        // | dif | u | r | - |

        self.combine(
            region,
            [
                Term::assigned_to_mul(&dif),
                Term::assigned_to_mul(&u),
                Term::assigned_to_add(&r),
                Term::Zero,
                Term::Zero,
            ],
            -one,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(r)
    }

    fn assert_zero(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.assert_equal_to_constant(region, a, F::zero(), offset)
    }

    fn assert_not_zero(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        // Non-zero element must have an inverse
        // a * w - 1 = 0

        let w = match a.value() {
            Some(a) => match a.invert().into() {
                Some(inverted) => Some(inverted),
                // Non inversion case will never be verified
                _ => Some(F::zero()),
            },
            _ => None,
        };

        self.combine(
            region,
            [
                Term::assigned_to_mul(&a),
                Term::unassigned_to_mul(w),
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            -F::one(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(())
    }

    fn is_zero(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<AssignedCondition<F>, Error> {
        let (_, is_zero) = self.invert(region, a, offset)?;
        Ok(is_zero)
    }

    fn assert_one(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.assert_equal_to_constant(region, a, F::one(), offset)
    }

    fn assert_equal_to_constant(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: F,
        offset: &mut usize,
    ) -> Result<(), Error> {
        self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::Zero,
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            -b,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(())
    }

    fn cond_or(
        &self,
        region: &mut Region<'_, F>,
        c1: &AssignedCondition<F>,
        c2: &AssignedCondition<F>,
        offset: &mut usize,
    ) -> Result<AssignedCondition<F>, Error> {
        let c = match (c1.value(), c2.value()) {
            (Some(c1), Some(c2)) => Some(c1 + c2 - c1 * c2),
            _ => None,
        };

        let zero = F::zero();

        // c + c1 * c2 - c1 - c2 = 0
        let cells = self.combine(
            region,
            [
                Term::assigned_to_sub(c1),
                Term::assigned_to_sub(c2),
                Term::unassigned_to_add(c),
                Term::Zero,
                Term::Zero,
            ],
            zero,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(AssignedCondition::new(cells.c, c))
    }

    fn cond_and(
        &self,
        region: &mut Region<'_, F>,
        c1: &AssignedCondition<F>,
        c2: &AssignedCondition<F>,
        offset: &mut usize,
    ) -> Result<AssignedCondition<F>, Error> {
        let c = match (c1.value(), c2.value()) {
            (Some(c1), Some(c2)) => Some(c1 * c2),
            _ => None,
        };

        let zero = F::zero();

        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(c1),
                Term::assigned_to_mul(c2),
                Term::unassigned_to_sub(c),
                Term::Zero,
                Term::Zero,
            ],
            zero,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(AssignedCondition::new(cells.c, c))
    }

    fn cond_not(
        &self,
        region: &mut Region<'_, F>,
        c: &AssignedCondition<F>,
        offset: &mut usize,
    ) -> Result<AssignedCondition<F>, Error> {
        let one = F::one();

        let not_c = match c.value() {
            Some(c) => Some(one - c),
            _ => None,
        };

        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(c),
                Term::unassigned_to_add(not_c),
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            -one,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        Ok(AssignedCondition::new(cells.b, not_c))
    }

    fn cond_select(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        cond: &AssignedCondition<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        // We should satisfy the equation below with bit asserted condition flag
        // c (a-b) + b - res = 0

        // Witness layout:
        // | A   | B   | C | D   |
        // | --- | --- | - | --- |
        // | dif | a   | b | -   |
        // | c   | dif | b | res |

        let (dif, res) = match (a.value(), b.value(), cond.bool_value) {
            (Some(a), Some(b), Some(cond)) => {
                let dif = a - b;
                let res = if cond { a } else { b };
                (Some(dif), Some(res))
            }
            _ => (None, None),
        };

        // a - b - dif = 0
        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::assigned_to_sub(&b),
                Term::Zero,
                Term::unassigned_to_sub(dif),
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        let dif = &mut AssignedValue::new(cells.d, dif);

        // cond * dif + b + a_or_b  = 0
        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(dif),
                Term::assigned_to_mul(cond),
                Term::assigned_to_add(&b),
                Term::unassigned_to_sub(res),
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        let res = AssignedValue::new(cells.d, res);

        Ok(res)
    }

    fn cond_select_or_assign(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: F,
        cond: &AssignedCondition<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        // We should satisfy the equation below with bit asserted condition flag
        // c (a-b_constant) + b_constant - res = 0

        // Witness layout:
        // | A   | B   | C | D   |
        // | --- | --- | - | --- |
        // | dif | a   | - | -   |
        // | c   | dif | - | res |

        let (dif, res) = match (a.value(), cond.bool_value) {
            (Some(a), Some(cond)) => {
                let dif = a - b;
                let res = if cond { a } else { b };
                (Some(dif), Some(res))
            }
            _ => (None, None),
        };

        // a - b - dif = 0
        let cells = self.combine(
            region,
            [
                Term::assigned_to_add(&a),
                Term::Zero,
                Term::Zero,
                Term::unassigned_to_sub(dif),
                Term::Zero,
            ],
            -b,
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;

        let dif = &mut AssignedValue::new(cells.d, dif);

        // cond * dif + b + a_or_b  = 0
        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(dif),
                Term::assigned_to_mul(cond),
                Term::Zero,
                Term::unassigned_to_sub(res),
                Term::Zero,
            ],
            b,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        let res = AssignedValue::new(cells.d, res);

        Ok(res)
    }

    fn assign_bit(
        &self,
        region: &mut Region<'_, F>,
        bit: &UnassignedValue<F>,
        offset: &mut usize,
    ) -> Result<AssignedBit<F>, Error> {
        // val * val - val  = 0

        // Witness layout:
        // | A   | B   | C   | D |
        // | --- | --- | --- | - |
        // | val | val | val | - |

        let cells = self.combine(
            region,
            [
                Term::unassigned_to_mul(bit.value()),
                Term::unassigned_to_mul(bit.value()),
                Term::unassigned_to_sub(bit.value()),
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        region.constrain_equal(cells.a, cells.b)?;
        region.constrain_equal(cells.b, cells.c)?;
        *offset = *offset + 1;

        Ok(AssignedBit::<F>::new(cells.c, bit.value()))
    }

    fn assert_bit(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        // val * val - val  = 0

        // Witness layout:
        // | A   | B   | C   | D |
        // | --- | --- | --- | - |
        // | val | val | val | - |

        let cells = self.combine(
            region,
            [
                Term::assigned_to_mul(&a),
                Term::assigned_to_mul(&a),
                Term::assigned_to_sub(&a),
                Term::Zero,
                Term::Zero,
            ],
            F::zero(),
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        region.constrain_equal(cells.a, cells.b)?;
        region.constrain_equal(cells.b, cells.c)?;
        *offset = *offset + 1;

        Ok(())
    }

    fn one_or_one(
        &self,
        region: &mut Region<'_, F>,
        a: impl Assigned<F>,
        b: impl Assigned<F>,
        offset: &mut usize,
    ) -> Result<(), Error> {
        // (a-1) * (b-1)  = 0

        // Witness layout:
        // | A   | B   | C   | D |
        // | --- | --- | --- | - |
        // | val | val | -   | - |

        let one = F::one();
        self.combine(
            region,
            [
                Term::assigned_to_sub(&a),
                Term::assigned_to_sub(&b),
                Term::Zero,
                Term::Zero,
                Term::Zero,
            ],
            one,
            offset,
            CombinationOptionCommon::OneLinerMul.into(),
        )?;

        Ok(())
    }

    fn combine(
        &self,
        region: &mut Region<'_, F>,
        terms: [Term<F>; WIDTH],
        constant_aux: F,
        offset: &mut usize,
        option: CombinationOption<F>,
    ) -> Result<AssignedCells, Error> {
        let (c_0, u_0) = (terms[0].coeff(), terms[0].base());
        let (c_1, u_1) = (terms[1].coeff(), terms[1].base());
        let (c_2, u_2) = (terms[2].coeff(), terms[2].base());
        let (c_3, u_3) = (terms[3].coeff(), terms[3].base());
        let (c_4, u_4) = (terms[4].coeff(), terms[4].base());

        let cell_0 = region
            .assign_advice(
                || "coeff_0",
                self.config.a,
                *offset,
                || Ok(c_0.ok_or(Error::Synthesis)?),
            )?
            .cell();
        let cell_1 = region
            .assign_advice(
                || "coeff_1",
                self.config.b,
                *offset,
                || Ok(c_1.ok_or(Error::Synthesis)?),
            )?
            .cell();
        let cell_2 = region
            .assign_advice(
                || "coeff_2",
                self.config.c,
                *offset,
                || Ok(c_2.ok_or(Error::Synthesis)?),
            )?
            .cell();
        let cell_3 = region
            .assign_advice(
                || "coeff_3",
                self.config.d,
                *offset,
                || Ok(c_3.ok_or(Error::Synthesis)?),
            )?
            .cell();
        let cell_4 = region
            .assign_advice(
                || "coeff_4",
                self.config.e,
                *offset,
                || Ok(c_4.ok_or(Error::Synthesis)?),
            )?
            .cell();

        region.assign_fixed(|| "base_0", self.config.sa, *offset, || Ok(u_0))?;
        region.assign_fixed(|| "base_1", self.config.sb, *offset, || Ok(u_1))?;
        region.assign_fixed(|| "base_2", self.config.sc, *offset, || Ok(u_2))?;
        region.assign_fixed(|| "base_3", self.config.sd, *offset, || Ok(u_3))?;
        region.assign_fixed(|| "base_4", self.config.se, *offset, || Ok(u_4))?;

        region.assign_fixed(
            || "s_constant",
            self.config.s_constant,
            *offset,
            || Ok(constant_aux),
        )?;

        match option {
            CombinationOption::Common(option) => match option {
                CombinationOptionCommon::CombineToNextMul(next) => {
                    region.assign_fixed(
                        || "s_mul_ab",
                        self.config.s_mul_ab,
                        *offset,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_mul_cd",
                        self.config.s_mul_cd,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(|| "se_next", self.config.se_next, *offset, || Ok(next))?;
                }

                CombinationOptionCommon::CombineToNextScaleMul(next, n) => {
                    region.assign_fixed(|| "s_mul_ab", self.config.s_mul_ab, *offset, || Ok(n))?;
                    region.assign_fixed(
                        || "s_mul_cd",
                        self.config.s_mul_cd,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(|| "se_next", self.config.se_next, *offset, || Ok(next))?;
                }
                CombinationOptionCommon::CombineToNextAdd(next) => {
                    region.assign_fixed(
                        || "s_mul_ab",
                        self.config.s_mul_ab,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(
                        || "s_mul_cd",
                        self.config.s_mul_cd,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(|| "se_next", self.config.se_next, *offset, || Ok(next))?;
                }
                CombinationOptionCommon::OneLinerMul => {
                    region.assign_fixed(
                        || "s_mul_ab",
                        self.config.s_mul_ab,
                        *offset,
                        || Ok(F::one()),
                    )?;
                    region.assign_fixed(
                        || "s_mul_cd",
                        self.config.s_mul_cd,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(
                        || "se_next",
                        self.config.se_next,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                }
                CombinationOptionCommon::OneLinerAdd => {
                    region.assign_fixed(
                        || "se_next",
                        self.config.se_next,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(
                        || "s_mul_ab",
                        self.config.s_mul_ab,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                    region.assign_fixed(
                        || "s_mul_cd",
                        self.config.s_mul_cd,
                        *offset,
                        || Ok(F::zero()),
                    )?;
                }
            },

            CombinationOption::CombineToNextDoubleMul(next) => {
                region.assign_fixed(
                    || "s_mul_ab",
                    self.config.s_mul_ab,
                    *offset,
                    || Ok(F::one()),
                )?;
                region.assign_fixed(
                    || "s_mul_cd",
                    self.config.s_mul_cd,
                    *offset,
                    || Ok(F::one()),
                )?;
                region.assign_fixed(|| "se_next", self.config.se_next, *offset, || Ok(next))?;
            }
            CombinationOption::OneLinerDoubleMul => {
                region.assign_fixed(
                    || "s_mul_ab",
                    self.config.s_mul_ab,
                    *offset,
                    || Ok(F::one()),
                )?;
                region.assign_fixed(
                    || "s_mul_cd",
                    self.config.s_mul_cd,
                    *offset,
                    || Ok(F::one()),
                )?;
                region.assign_fixed(
                    || "se_next",
                    self.config.se_next,
                    *offset,
                    || Ok(F::zero()),
                )?;
            }
        };

        terms[0].constrain_equal(region, cell_0)?;
        terms[1].constrain_equal(region, cell_1)?;
        terms[2].constrain_equal(region, cell_2)?;
        terms[3].constrain_equal(region, cell_3)?;
        terms[4].constrain_equal(region, cell_4)?;

        *offset = *offset + 1;

        Ok(AssignedCells::new(cell_0, cell_1, cell_2, cell_3, cell_4))
    }

    fn assign_value(
        &self,
        region: &mut Region<'_, F>,
        unassigned: &UnassignedValue<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        self.assign_to_column(region, unassigned, MainGateColumn::A, offset)
    }

    fn assign_to_column(
        &self,
        region: &mut Region<'_, F>,
        unassigned: &UnassignedValue<F>,
        column: MainGateColumn,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        let column = match column {
            MainGateColumn::A => self.config.a,
            MainGateColumn::B => self.config.b,
            MainGateColumn::C => self.config.c,
            MainGateColumn::D => self.config.d,
            MainGateColumn::E => self.config.e,
        };
        let cell = region.assign_advice(
            || "assign value",
            column,
            *offset,
            || unassigned.value().ok_or(Error::Synthesis),
        )?;
        // proceed to the next row
        self.no_operation(region, offset)?;

        Ok(unassigned.assign(cell.cell()))
    }

    fn assign_to_acc(
        &self,
        region: &mut Region<'_, F>,
        unassigned: &UnassignedValue<F>,
        offset: &mut usize,
    ) -> Result<AssignedValue<F>, Error> {
        self.assign_to_column(region, unassigned, MainGateColumn::E, offset)
    }

    fn no_operation(&self, region: &mut Region<'_, F>, offset: &mut usize) -> Result<(), Error> {
        region.assign_fixed(
            || "s_mul_ab",
            self.config.s_mul_ab,
            *offset,
            || Ok(F::zero()),
        )?;
        region.assign_fixed(
            || "s_mul_cd",
            self.config.s_mul_cd,
            *offset,
            || Ok(F::zero()),
        )?;
        region.assign_fixed(|| "sc", self.config.sc, *offset, || Ok(F::zero()))?;
        region.assign_fixed(|| "sa", self.config.sa, *offset, || Ok(F::zero()))?;
        region.assign_fixed(|| "sb", self.config.sb, *offset, || Ok(F::zero()))?;
        region.assign_fixed(|| "sd", self.config.sd, *offset, || Ok(F::zero()))?;
        region.assign_fixed(|| "se", self.config.se, *offset, || Ok(F::zero()))?;
        region.assign_fixed(|| "se_next", self.config.se_next, *offset, || Ok(F::zero()))?;
        region.assign_fixed(
            || "s_constant",
            self.config.s_constant,
            *offset,
            || Ok(F::zero()),
        )?;
        *offset = *offset + 1;
        Ok(())
    }

    #[cfg(test)]
    fn break_here(&self, region: &mut Region<'_, F>, offset: &mut usize) -> Result<(), Error> {
        self.combine(
            region,
            [Term::Zero, Term::Zero, Term::Zero, Term::Zero, Term::Zero],
            F::one(),
            offset,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?;
        *offset = *offset + 1;
        Ok(())
    }
}

impl<F: FieldExt> MainGate<F> {
    pub fn new(config: MainGateConfig) -> Self {
        MainGate {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MainGateConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let d = meta.advice_column();
        let e = meta.advice_column();

        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let sd = meta.fixed_column();
        let se = meta.fixed_column();

        let s_mul_ab = meta.fixed_column();
        let s_mul_cd = meta.fixed_column();

        let se_next = meta.fixed_column();
        let s_constant = meta.fixed_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(d);
        meta.enable_equality(e);

        meta.create_gate("main_gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let d = meta.query_advice(d, Rotation::cur());
            let e_next = meta.query_advice(e, Rotation::next());
            let e = meta.query_advice(e, Rotation::cur());

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sd = meta.query_fixed(sd, Rotation::cur());
            let se = meta.query_fixed(se, Rotation::cur());

            let se_next = meta.query_fixed(se_next, Rotation::cur());

            let s_mul_ab = meta.query_fixed(s_mul_ab, Rotation::cur());
            let s_mul_cd = meta.query_fixed(s_mul_cd, Rotation::cur());

            let s_constant = meta.query_fixed(s_constant, Rotation::cur());

            vec![
                a.clone() * sa
                    + b.clone() * sb
                    + c.clone() * sc
                    + d.clone() * sd
                    + e * se
                    + a * b * s_mul_ab
                    + c * d * s_mul_cd
                    + se_next * e_next
                    + s_constant,
            ]
        });

        MainGateConfig {
            a,
            b,
            c,
            d,
            e,
            sa,
            sb,
            sc,
            sd,
            se,
            se_next,
            s_constant,
            s_mul_ab,
            s_mul_cd,
        }
    }
}
