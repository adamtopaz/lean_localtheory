import tactic
import algebra
import data.zmod.basic
import data.nat.prime
import .log

instance is_prime_2 : fact (nat.prime 2) := nat.prime_two

@[simp] lemma zmod2_eq_zero_iff_ne_one {a : zmod 2} : ¬ (a = 1) ↔ a = 0 := by {fin_cases a, tidy}

@[simp] lemma zmod2_eq_one_of_ne_zero {a : zmod 2} : ¬ (a = 0) ↔ a = 1 := by {fin_cases a, tidy}

@[simp] lemma zmod2_2_eq_0 : (2 : zmod 2) = 0 := rfl

@[simp] lemma zmod2_add_self {a : zmod 2} : a + a = 0 := by {rw (show a + a = 2 * a, by ring), simp}

variables {K : Type*} [field K]

lemma neg_one_mem_ker (f : log K (zmod 2)) (cond : ∃ a : K, a * a = -1) : (-1 : K) ∈ f.ker :=
begin
  rcases cond with ⟨a,ha⟩,
  rw ← ha,
  simp,
  intro c,
  finish [c],
end
