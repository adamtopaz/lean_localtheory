import .maintheorem
import .altpairs
import data.zmod.basic
import data.nat.prime

instance is_prime_2 : fact (nat.prime 2) := nat.prime_two

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
      split,
      intro c,
      simpa [c] using ha,
      rw (show f a + f a = 2 * f a, by ring),
      rw (show (2 : zmod 2) = 0, by dec_trivial),
      simp },
    { simp,
      split,
      intro c,
      simpa [c] using ha,
      rw (show g a + g a = 2 * g a, by ring),
      rw (show (2 : zmod 2) = 0, by dec_trivial),
      simp }
  },
  { sorry }
end
