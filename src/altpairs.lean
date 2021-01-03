import .mult_subgroup.basic
import tactic
import algebra

@[ext]
structure log (K F : Type*) [field K] [field F] :=
(to_fun : K → F)
(map_one' : to_fun 1 = 0)
(map_mul' (x y) : to_fun (x * y) = to_fun x + to_fun y)
(map_zero' : to_fun 0 = 0) -- junk value

variables {K F : Type*} [field K] [field F] (f : log K F)

namespace log

instance : has_coe_to_fun (log K F) := ⟨_,to_fun⟩

@[simp] lemma to_fun_eq : f.to_fun = f := rfl

@[simp] lemma map_one : f 1 = 0 := f.map_one'
@[simp] lemma map_mul (x y : K) : f (x * y) = f x + f y := f.map_mul' _ _
@[simp] lemma map_zero : f 0 = 0 := f.map_zero'

@[simp] lemma map_inv (x : K) : f (x⁻¹) = -(f x) :=
begin
  rw eq_neg_iff_add_eq_zero,
  rw ← log.map_mul,
  by_cases h : x = 0,
  { simp [h] },
  { simp [inv_mul_cancel h] },
end

@[simps]
instance : has_add (log K F) :=
{ add := λ f g,
  { to_fun := λ x, f x + g x,
    map_one' := by simp,
    map_mul' := λ x y, by simp; ring,
    map_zero' := by simp } }

@[simps]
instance : has_zero (log K F) := has_zero.mk $
{ to_fun := λ _, 0,
  map_one' := rfl,
  map_mul' := λ _ _, by simp,
  map_zero' := rfl }

@[simps]
instance : has_neg (log K F) := has_neg.mk $ λ f,
{ to_fun := λ x, -(f x),
  map_one' := by simp,
  map_mul' := λ x y, by simp; ring,
  map_zero' := by simp }

instance : add_comm_group (log K F) :=
{ add_assoc := λ f g h, by {ext, simp [add_assoc]},
  zero_add := λ a, by {ext, simp},
  add_zero := λ a, by {ext, simp},
  add_left_neg := λ f, by {ext, simp},
  add_comm := λ f g, by {ext, simp [add_comm]},
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _),
  ..(infer_instance : has_neg _) }

@[simps]
instance : has_scalar F (log K F) := has_scalar.mk $ λ a f,
{ to_fun := λ x, a * f x,
  map_one' := by simp,
  map_mul' := λ a b, by simp [mul_add],
  map_zero' := by simp }

instance : module F (log K F) :=
{ one_smul := λ f, by {ext, simp},
  mul_smul := λ a b f, by {ext, simp [mul_assoc]},
  smul_add := λ a f g, by {ext, simp [mul_add]},
  smul_zero := λ a, by {ext, simp},
  add_smul := λ a b f, by {ext, simp [add_mul]},
  zero_smul := λ f, by {ext, simp} }

def ker (f : log K F) : mult_subgroup K :=
{ carrier := {x | x ≠ 0 ∧ f x = 0},
  zero_nmem' := λ c, c.1 rfl,
  one_mem' := ⟨one_ne_zero, by simp⟩,
  mul_mem' := λ x y ⟨h1,h2⟩ ⟨h3,h4⟩, ⟨mul_ne_zero h1 h3, by simp [h2, h4]⟩,
  inv_mem' := λ x ⟨h1,h2⟩, ⟨inv_ne_zero h1, by simpa⟩ }

@[simp] lemma mem_ker_iff {x : K} : x ∈ f.ker ↔ x ≠ 0 ∧ f x = 0 := by tidy

@[simp] lemma nmem_ker_iff {x : K} : x ∉ f.ker ↔ x = 0 ∨ f x ≠ 0 :=
begin
  erw mem_ker_iff,
  simp,
  tauto,
end

end log

def alternating (f g : log K F) : Prop := ∀ x : K, f x * g (1 - x) = f (1 - x) * g x
