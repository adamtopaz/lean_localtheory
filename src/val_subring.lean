import .mult_subgroup.basic
import ring_theory.subring
import algebra

variables (K : Type*) [field K]

/--
A "valuation subring" of a field `K` is a subring `R`
of `K`, such that for every element `x` of `K`,
either `x` is contained in `R` or its inverse is
is contained in `R`.
-/
structure val_subring extends subring K :=
(val_cond {x : K} : x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace val_subring
variables {K} (R : val_subring K)

instance : has_mem K (val_subring K) := ⟨λ x R, x ∈ R.carrier⟩

-- 𝒪^×, the units of 𝒪.
-- This is a multiplicative subgroup of K.
def units : set K := {x | x ≠ 0 ∧ x ∈ R ∧ x⁻¹ ∈ R}

def units' : mult_subgroup K :=
{ carrier := R.units,
  zero_nmem' := λ c, c.1 rfl,
  one_mem' := begin
    refine ⟨one_ne_zero, subring.one_mem _, _⟩,
    simp,
    exact subring.one_mem _,
  end,
  mul_mem' := λ x y hx hy, begin
    refine ⟨mul_ne_zero hx.1 hy.1, subring.mul_mem _ hx.2.1 hy.2.1, _⟩,
    simp [mul_inv'],
    refine subring.mul_mem _ hx.2.2 hy.2.2,
  end,
  inv_mem' := λ x hx, begin
    refine ⟨inv_ne_zero hx.1, hx.2.2, _⟩,
    simp,
    exact hx.2.1,
  end }

-- 𝔪, the maximal ideal of 𝒪. This is an ideal of 𝒪.
def maximal_ideal : set K := {x | x ∈ R ∧ x ∈ R.unitsᶜ}

-- 1 + 𝔪, the principal units of 𝒪.
-- This is a multiplicative subgroup of K, contains in 𝒪^×.
def principal_units : set K := {x | x - 1 ∈ R.maximal_ideal}

end val_subring
