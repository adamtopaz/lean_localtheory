import .maintheorem
import .altpairs
import data.zmod.basic
import data.nat.prime

instance is_prime_2 : fact (nat.prime 2) := nat.prime_two

@[simp] lemma zmod2_eq_zero_iff_ne_one {a : zmod 2} : ¬ (a = 1) ↔ a = 0 := by {fin_cases a, tidy}

@[simp] lemma zmod2_eq_one_of_ne_zero {a : zmod 2} : ¬ (a = 0) ↔ a = 1 := by {fin_cases a, tidy}

@[simp] lemma zmod2_2_eq_0 : (2 : zmod 2) = 0 := rfl

@[simp] lemma zmod2_add_self {a : zmod 2} : a + a = 0 := by {rw (show a + a = 2 * a, by ring), simp}

variables (K : Type*) [field K]
variables (f g : log K (zmod 2))
variable (cond : ∃ a : K, a * a = -1)
variable (alt : alternating f g)

include alt cond

/--
This is the fundamental theorem of alternating pairs, in the `zmod 2` case.
-/
theorem alt_pair_theorem : ∃ (R : val_subring K) (a b : zmod 2),
  (a ≠ 0 ∨ b ≠ 0) ∧
  R.principal_units ⊆ f.ker ⊓ g.ker ∧
  R.units ⊆ (a • f + b • g).ker :=
begin
  let T := f.ker ⊓ g.ker,
  have := maintheorem K T T T.le_refl _ _,
  rcases this with ⟨R,x,h1,h2,h3,h4⟩,
  use R,
  { set a := f x with ha,
    set b := g x with hb,
    fin_cases a; fin_cases b,
    { use 1, use 0,
      refine ⟨or.inl one_ne_zero, h4, _⟩,
      have : T.adjoin h1 ≤ f.ker,
      { apply T.adjoin_le_of_mem,
        exact mult_subgroup.inf_le_left _ _,
        simp,
        refine ⟨h1, _⟩,
        simpa [← ha] },
      simp,
      exact λ _ hu, this (h3 hu) },
    { change b = 1 at h_1,
      use 1, use 0,
      refine ⟨or.inl one_ne_zero, h4, _⟩,
      simp,
      have : T.adjoin h1 ≤ f.ker,
      { apply T.adjoin_le_of_mem,
        exact mult_subgroup.inf_le_left _ _,
        simp,
        refine ⟨h1, _⟩,
        simpa [← ha] },
      exact λ _ hu, this (h3 hu) },
    { change a = 1 at h,
      use 0, use 1,
      refine ⟨or.inr one_ne_zero, h4, _⟩,
      simp,
      have : T.adjoin h1 ≤ g.ker,
      { apply T.adjoin_le_of_mem,
        apply mult_subgroup.inf_le_right,
        simp,
        refine ⟨h1, _⟩,
        simpa [← hb] },
      exact λ _ hu, this (h3 hu) },
    { change a = 1 at h,
      change b = 1 at h_1,
      use 1, use 1,
      refine ⟨or.inl one_ne_zero, h4, _⟩,
      simp,
      have : T.adjoin h1 ≤ (f + g).ker,
      { apply T.adjoin_le_of_mem,
        intros t ht,
        change _ ∈ (f + g).ker, -- missing simp lemma
        cases ht with ht1 ht2,
        simp at ht1 ht2 ⊢,
        refine ⟨ht1.1, _⟩,
        simp [ht1.2, ht2.2],
        refine ⟨h1, _⟩,
        simp [← ha, ← hb, h, h_1] },
      exact λ _ hu, this (h3 hu) } },
  { rcases cond with ⟨a,ha⟩,
    rw ← ha,
    split,
    all_goals { simp,
      intro c,
      simpa [c] using ha }},
  { intros x hx,
    by_cases hxnez : x = 0,
    { left, simp [hxnez, T.one_mem] },
    have hx2 : 1 - x ≠ 0,
    { intro c,
      apply_fun (λ t, t + x) at c,
      simp at c,
      rw ← c at hx,
      exact hx T.one_mem },
    erw not_and_distrib at hx,
    cases hx,
    { simp at hx,
      specialize hx hxnez,
      specialize alt x,
      rw [hx, one_mul] at alt,
      by_cases hfox : f (1 - x) = 0,
      { simp [hfox] at alt,
        left,
        split; simp,
        refine ⟨hx2, hfox⟩,
        refine ⟨hx2, alt⟩ },
      simp at hfox,
      simp [hfox] at alt,
      right,
      rw T.mem_coset_iff hxnez,
      split,
      simp [not_or_distrib],
      refine ⟨⟨hxnez, hx2⟩,_⟩,
      simp [hx, hfox],
      simp [not_or_distrib],
      refine ⟨⟨hxnez, hx2⟩,_⟩,
      simp [alt] },
    { simp at hx,
      specialize hx hxnez,
      specialize alt x,
      rw [hx, mul_one] at alt,
      by_cases hgox : g (1 - x) = 0,
      { simp [hgox] at alt,
        left,
        split; simp,
        refine ⟨hx2, alt.symm⟩,
        refine ⟨hx2, hgox⟩ },
      simp at hgox,
      simp [hgox] at alt,
      right,
      rw T.mem_coset_iff hxnez,
      split,
      simp [not_or_distrib],
      refine ⟨⟨hxnez, hx2⟩,_⟩,
      simp [alt],
      simp [not_or_distrib],
      refine ⟨⟨hxnez, hx2⟩,_⟩,
      simp [hx, hgox] } }
end
