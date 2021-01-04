import linear_algebra
import .log
import .mult_subgroup.basic

open_locale classical

variables {K F : Type*} [field K] [field F]

namespace mult_subgroup

@[simps] def orthog (H : mult_subgroup K) : submodule F (log K F) :=
{ carrier := {f | ∀ {x : K}, x ∈ H → f x = 0},
  zero_mem' := λ _ _, by simp,
  add_mem' := λ f g hf hg x hx, by simp [hf hx, hg hx],
  smul_mem' := λ c f hf x hx, by simp [hf hx] }

end mult_subgroup

namespace log

variables (K F)
abbreviation subspace := submodule F (log K F)
variables {K F}

namespace subspace

@[simps] def orthog (M : log.subspace K F) : mult_subgroup K :=
{ carrier := {x | x ≠ 0 ∧ ∀ {f : log K F}, f ∈ M → f x = 0},
  zero_nmem' := λ c, c.1 rfl,
  one_mem' := ⟨one_ne_zero,λ f hf, by simp⟩,
  mul_mem' := λ x y hx hy, ⟨mul_ne_zero hx.1 hy.1, λ f hf, by simp [hx.2 hf, hy.2 hf]⟩,
  inv_mem' := λ x hx, ⟨inv_ne_zero hx.1, λ f hf, by simp [hx.2 hf]⟩ }

end subspace

end log
