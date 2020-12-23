import ring_theory.subring
import algebra

variables (K : Type*) [field K]

structure val_subring extends subring K :=
(val_cond {x : K} : x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace val_subring
variables {K} (R : val_subring K)

instance : has_mem K (val_subring K) := ⟨λ x R, x ∈ R.carrier⟩

def units : set K := {x | x ≠ 0 ∧ x ∈ R ∧ x⁻¹ ∈ R}
def maximal_ideal : set K := {x | x ∈ R ∧ x ∈ R.unitsᶜ}
def principal_units : set K := {x | x - 1 ∈ R.maximal_ideal}

end val_subring
