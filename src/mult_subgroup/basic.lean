import algebra
import tactic.field_simp
import tactic

variables (K : Type*) [field K]

@[ext]
structure mult_subgroup :=
(carrier : set K)
(zero_nmem' : (0 : K) ∉ carrier)
(one_mem' : (1 : K) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

namespace mult_subgroup

instance : has_mem K (mult_subgroup K) := ⟨λ x H, x ∈ H.carrier⟩
instance : has_le (mult_subgroup K) := ⟨λ T H, T.carrier ≤ H.carrier⟩
instance : has_coe (mult_subgroup K) (set K) := ⟨carrier⟩

variables (H : mult_subgroup K) {K}

lemma le_trans {A B C : mult_subgroup K} : A ≤ B → B ≤ C → A ≤ C := λ h1 h2 x hx, h2 $ h1 hx

lemma zero_nmem : (0 : K) ∉ H := H.zero_nmem'

lemma one_mem : (1 : K) ∈ H := H.one_mem'

lemma mul_mem {x y : K} : x ∈ H → y ∈ H → x * y ∈ H := λ h1 h2, H.mul_mem' h1 h2

lemma inv_mem {x : K} : x ∈ H → x⁻¹ ∈ H := λ h, H.inv_mem' h

lemma inv_nmem {x : K} : x ∉ H → x⁻¹ ∉ H :=
  λ h c, let h := H.inv_mem c in by finish

lemma ne_zero {x : K} : x ∈ H → x ≠ 0 :=
  λ h c, by {rw c at *, finish [H.zero_nmem]}

lemma mem_of_inv_mem {x : K} : x⁻¹ ∈ H → x ∈ H :=
  λ h, by {rw ← inv_inv' x, exact H.inv_mem h}

lemma mem_of_mul_mem_mem_left {x y : K} : x * y ∈ H → y ∈ H → x ∈ H :=
begin
  intros h hy,
  rw (show x = x * y * y⁻¹,
    by simp [mul_assoc, mul_inv_cancel (H.ne_zero hy)]),
  exact mul_mem H h (inv_mem H hy)
end

lemma mem_of_mul_mem_mem_right {x y : K} : x * y ∈ H → x ∈ H → y ∈ H :=
begin
  intros h hx,
  rw mul_comm at h,
  exact mem_of_mul_mem_mem_left _ h hx,
end

lemma nmem_of_mul_nmem_left {x y : K} : x * y ∉ H → y ∈ H → x ∉ H :=
  λ h1 h2 c, h1 (mul_mem  H c h2)

lemma nmem_of_mul_nmem_right {x y : K} : x * y ∉ H → x ∈ H → y ∉ H :=
  λ h1 h2 c, h1 (mul_mem _ h2 c)

lemma mul_inv_mem {x y : K} : x ∈ H → y ∈ H → x * y⁻¹ ∈ H :=
  λ hx hy, mul_mem _ hx $ inv_mem _ hy

lemma inv_mul_mem {x y : K} : x ∈ H → y ∈ H → x⁻¹ * y ∈ H :=
  λ hx hy, mul_mem _ (inv_mem _ hx) hy

lemma mul_nmem_of_mem_nmem {x y : K} : x ∈ H → y ∉ H → x * y ∉ H :=
  λ hx hy c, hy (mem_of_mul_mem_mem_right H c hx)

lemma mul_nmem_of_nmem_mem {x y : K} : x ∉ H → y ∈ H → x * y ∉ H :=
  λ hx hy c, hx (mem_of_mul_mem_mem_left H c hy)

protected lemma mul_inv_cancel {x : K} : x ∈ H → x * x⁻¹ = 1 := λ h,
  mul_inv_cancel $ H.ne_zero h

protected lemma inv_mul_cancel {x : K} : x ∈ H → x⁻¹ * x = 1 := λ h,
  inv_mul_cancel $ H.ne_zero h

lemma ne_zero_of_one_minus_mul_left {a b : K} : 1 - a * b ∉ H → a ≠ 0 :=
λ h c, h $ by simp [c, H.one_mem]

lemma ne_zero_of_one_minus_mul_right {a b : K} : 1 - a * b ∉ H → b ≠ 0 :=
λ h c, h $ by simp [c, H.one_mem]

end mult_subgroup
