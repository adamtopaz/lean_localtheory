import .maintheorem
import .log
import .zmod2_helpers

/-!
This is a formalization of the "theory of rigid elements" based on the following references:

1. Ware. "Valuation rings and rigid elements in fields." Canad. J. Math. 33 (1981)
2. Arason, Elman, Jacob. "Rigid Elements, Valuations, and Realization of Witt Rings". J. Algebra 110 (1987)
-/

--variables (K : Type*) [field K]
--variables (f g : log K (zmod 2))
--variables (cond : ∃ a : K, a * a = -1)
--variables (alt : ∀ x : K, f x *  g (1 - x) = f (1 - x) * g x) -- Steinberg alternating condition.

--include alt cond

--#check log
--#check val_subring
--#check mult_subgroup
--#check mult_subgroup.adjoin -- adjoin element to mult_subgroup
--#check mult_subgroup.rigid
--#check mult_subgroup.birigid
--#check rig_pair
--#check rig_pair.adjoin -- adjoin element to R.H for R : rig_pair
--#check rig_pair.OO
--#check preadd
--#check to_val
--#check index_two
--#check maintheorem

--example : ∃ (R : val_subring K) (a b : zmod 2),
--  (a ≠ 0 ∨ b ≠ 0) ∧
--  R.principal_units ⊆ f.ker ⊓ g.ker ∧
--  R.units ⊆ (a • f + b • g).ker :=
--begin
--  sorry
  /-
  let T := f.ker ⊓ g.ker,
  have := maintheorem K T T T.le_refl
    ⟨neg_one_mem_ker _ cond, neg_one_mem_ker _ cond⟩ _,
  rcases this with ⟨R,x,h1,h2,h3,h4⟩,
  use R,
  { set a := f x with ha,
    set b := g x with hb,
    fin_cases a; fin_cases b,
    { refine ⟨1,0,or.inl one_ne_zero, h4, λ _ hu, _⟩,
      simp,
      refine (sub_lin_comb_left_helper _ _ _ _) (h3 hu),
      simp [← ha, h] },
    { refine ⟨1,0,or.inl one_ne_zero, h4, λ _ hu, _⟩,
      simp,
      refine (sub_lin_comb_left_helper _ _ _ _) (h3 hu),
      simp [← ha, h] },
    { refine ⟨0,1,or.inr one_ne_zero, h4, λ _ hu, _⟩,
      simp,
      refine (sub_lin_comb_right_helper _ _ _ _) (h3 hu),
      simp [← hb, h_1] },
    { refine ⟨1,1,or.inl one_ne_zero, h4, λ _ hu, _⟩,
      simp,
      refine (sub_lin_comb_helper _ _ _ _ _) (h3 hu),
      simpa [← ha, ← h],
      simpa [← hb, ← h_1] } },
  { intros x hx,
    by_cases hxnez : x = 0, { left, simp [hxnez, T.one_mem] },
    have hx2 : 1 - x ≠ 0, { intro c, rw sub_eq_zero at c, rw ← c at hx, exact hx T.one_mem },
    erw not_and_distrib at hx,
    simp at hx,
    cases hx; specialize hx hxnez; specialize alt x; simp [hx] at alt,
    { by_cases hfx : f (1 - x) = 0, { simp [hfx] at alt, refine or.inl ⟨⟨hx2,hfx⟩,⟨hx2,alt⟩⟩ },
      simp at hfx,
      simp [hfx] at alt,
      right,
      rw T.mem_coset_iff hxnez,
      split; simp [not_or_distrib]; refine ⟨⟨hxnez, hx2⟩,_⟩; simp [hx, hfx, alt] },
    { by_cases hgx : g (1 - x) = 0, { simp [hgx] at alt, refine or.inl ⟨⟨hx2, alt.symm⟩, ⟨hx2, hgx⟩⟩ },
      simp at hgx,
      simp [hgx] at alt,
      right,
      rw T.mem_coset_iff hxnez,
      split; simp [not_or_distrib]; refine ⟨⟨hxnez, hx2⟩, _⟩; simp [hx, hgx, alt] } }
  -/
--end
