import .maintheorem
import .altpairs
import data.zmod.basic
import data.nat.prime

instance is_prime_2 : fact (nat.prime 2) := nat.prime_two

@[simp] lemma zmod2_eq_zero_iff_ne_one {a : zmod 2} : ¬ (a = 1) ↔ a = 0 := sorry

@[simp] lemma zmod2_eq_one_of_ne_zero {a : zmod 2} : ¬ (a = 0) ↔ a = 1 := sorry

@[simp] lemma zmod2_2_eq_0 : (2 : zmod 2) = 0 := rfl

@[simp] lemma zmod2_add_self {a : zmod 2} : a + a = 0 := by {rw (show a + a = 2 * a, by ring), simp}

variables (K : Type*) [field K]
variables (f g : log K (zmod 2))
variable (cond : ∃ a : K, a * a = -1)
variable (alt : alternating f g)

include alt cond

theorem alt_pair_theorem : ∃ (R : val_subring K) (a b : zmod 2),
  (a ≠ 0 ∨ b ≠ 0) ∧
  R.principal_units ⊆ f.ker ⊓ g.ker ∧
  R.units ⊆ (a • f + b • g).ker :=
begin
  let T := f.ker ⊓ g.ker,
  have := maintheorem K T T T.le_refl _ _,
  rcases this with ⟨R,x,h1,h2,h3,h4⟩,
  use R,
  { sorry },
  { rcases cond with ⟨a,ha⟩,
    rw ← ha,
    split,
    { simp,
      intro c,
      simpa [c] using ha },
    { simp,
      intro c,
      simpa [c] using ha }},
  { intros x hx,
    by_cases hxnez : x = 0,
    { left, simp [hxnez, T.one_mem] },
    erw not_and_distrib at hx,
    cases hx,
    { simp at hx,
      specialize hx hxnez,
      specialize alt x,
      rw [hx, one_mul] at alt,
      have hx2 : 1 - x ≠ 0,
      { intro c,
        apply_fun (λ t, t + x) at c,
        simp at c,
        rw ← c at hx,
        simpa using hx },
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
    { sorry }
  }
end
