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

-- 𝔪, the maximal ideal of 𝒪. This is an ideal of 𝒪.
def maximal_ideal : set K := {x | x ∈ R ∧ x ∈ R.unitsᶜ}

-- 1 + 𝔪, the principal units of 𝒪.
-- This is a multiplicative subgroup of K, contains in 𝒪^×.
def principal_units : set K := {x | x - 1 ∈ R.maximal_ideal}

end val_subring
