import tactic.field_simp
import tactic
import algebra

variables {K : Type*} [field K]

@[simp]
def rigtrans (x : K) : K := (-x) * (1 + x)⁻¹

lemma ne_neg_one_iff {x : K} : x ≠ -1 ↔ 1 + x ≠ 0 :=
begin
  change (¬ _) ↔ _,
  rw eq_neg_iff_add_eq_zero,
  finish,
end

lemma rigtrans_rigtrans {x : K} (hx : x ≠ -1) : rigtrans (rigtrans x) = x := by field_simp [ne_neg_one_iff.mp hx]
