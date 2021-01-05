import tactic
import algebra
import data.zmod.basic
import data.nat.prime
import .log
import .mult_subgroup.adjoin

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

lemma sub_lin_comb_left_helper (f g : log K (zmod 2)) {x : K} (hx : x ≠ 0) :
  f x = 0 → (f.ker ⊓ g.ker).adjoin hx ≤ f.ker :=
begin
  intro hfx,
  apply mult_subgroup.adjoin_le_of_mem,
  apply mult_subgroup.inf_le_left _ _,
  exact ⟨hx,hfx⟩,
end

lemma sub_lin_comb_right_helper (f g : log K (zmod 2)) {x : K} (hx : x ≠ 0) :
  g x = 0 → (f.ker ⊓ g.ker).adjoin hx ≤ g.ker :=
begin
  intro hfx,
  apply mult_subgroup.adjoin_le_of_mem,
  apply mult_subgroup.inf_le_right _ _,
  exact ⟨hx,hfx⟩,
end

lemma sub_lin_comb_helper (f g : log K (zmod 2)) {x : K} (hx : x ≠ 0) :
  f x ≠ 0 → g x ≠ 0 → (f.ker ⊓ g.ker).adjoin hx ≤ (f + g).ker :=
begin
  intros hfx hgx,
  simp at hfx hgx,
  apply mult_subgroup.adjoin_le_of_mem,
  { intros u hu,
    change _ ∈ (f+g).ker,
    change _ ∈ (f.ker ⊓ g.ker) at hu, -- missing simp lemmas
    refine ⟨mult_subgroup.ne_zero _ hu, _⟩,
    simp [hu.1.2, hu.2.2] },
  { refine ⟨hx,_⟩,
    simp [hfx, hgx] }
end
