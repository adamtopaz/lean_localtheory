import .basic

variables {K : Type*} [field K] (H : mult_subgroup K)

namespace mult_subgroup

def coset (x : K) : set K := {y | ∃ h ∈ H, y = x * h}

lemma gen_mem {x : K} : x ∈ H.coset x := ⟨1,H.one_mem,by simp⟩

lemma coset_ne_zero {x y : K} (hx : x ≠ 0) : y ∈ H.coset x → y ≠ 0 :=
begin
  rintro ⟨w,h,rfl⟩,
  exact mul_ne_zero hx (H.ne_zero h)
end

@[simp] lemma coset_one : H.coset 1 = H :=
begin
  ext,
  split,
  { rintro ⟨u,hu,rfl⟩,
    simpa },
  { intro h,
    refine ⟨x, h, by simp⟩ }
end

@[simp] lemma coset_zero : H.coset 0 = {0} :=
begin
  ext,
  split,
  { rintro ⟨u,hu,rfl⟩,
    simp },
  { intro h,
    refine ⟨1, H.one_mem, by simpa⟩ }
end

lemma ne_zero_of_mem {x y : K} (hx : x ≠ 0) : y ∈ H.coset x → y ≠ 0 :=
begin
  rintro ⟨z,hz,rfl⟩,
  exact mul_ne_zero hx (H.ne_zero hz)
end

lemma ne_zero_of_mem' {x y : K} (hx : x ≠ 0) : x ∈ H.coset y → y ≠ 0 :=
begin
  rintro ⟨z,hz,rfl⟩ c,
  exact hx (by simp [c]),
end

lemma mem_coset_iff {x y : K} (hx : x ≠ 0) : y ∈ H.coset x ↔ x⁻¹ * y ∈ H :=
begin
  split,
  { rintro ⟨z,hz,rfl⟩,
    rw [← mul_assoc, inv_mul_cancel hx],
    simpa },
  { intro h,
    refine ⟨x⁻¹ * y, h, _⟩,
    field_simp [hx],
    ring }
end

lemma coset_eq_mul {x y : K} (h : y ∈ H) : H.coset x = H.coset (x * y) :=
begin
  by_cases hx : x = 0,
  { rw hx, simp },
  ext z,
  split,
  { intro hzx,
    have hz := H.ne_zero_of_mem hx hzx,
    rw H.mem_coset_iff at hzx ⊢,
    rw (show (x * y)⁻¹ * z = x⁻¹ * z * y⁻¹, by simp [mul_inv']; ring),
    exact H.mul_mem hzx (H.inv_mem h),
    refine mul_ne_zero hx (H.ne_zero h),
    exact hx },
  { intro hzxy,
    rw H.mem_coset_iff at hzxy ⊢,
    rw (show (x * y)⁻¹ * z = x⁻¹ * z * y⁻¹, by simp [mul_inv']; ring) at hzxy,
    refine H.mem_of_mul_mem_mem_left hzxy (H.inv_mem h),
    exact hx,
    refine mul_ne_zero hx (H.ne_zero h) },
end

lemma coset_nmem_of_mem {x y : K} (hx : x ∉ H) : y ∈ H.coset x → y ∉ H :=
begin
  rintro ⟨z,hz,rfl⟩,
  exact H.mul_nmem_of_nmem_mem hx hz,
end

lemma coset_nmem_of_mem' {x y : K} (hx : x ∉ H) : y ∈ H → y ∉ H.coset x :=
begin
  intros h c,
  rw H.mem_coset_iff at c,
  refine (H.mul_nmem_of_nmem_mem (H.inv_nmem hx) h) c,
  intro cc,
  simp [cc] at c,
  finish [H.ne_zero h],
end

lemma mem_zero_iff {a : K} : (0 : K) ∈ H.coset a ↔ a = 0 :=
begin
  split,
  { rintro ⟨x,h1,h2⟩,
    simp at h2,
    cases h2,
    assumption,
    finish [H.zero_nmem] },
  { intro c,
    rw c,
    simp },
end

@[simp] lemma mem_zero_iff' {a : K} : ({0} : set K) = H.coset a ↔ a = 0 :=
begin
  split,
  { intro h,
    have : (0 : K) ∈ H.coset a,
    rw ← h, simp,
    rwa ← mem_zero_iff },
  { intro h,
    rw h,
    simp }
end

lemma coset_eq_iff {a b : K} (ha : a ≠ 0) : H.coset a = H.coset b ↔ b * a⁻¹ ∈ H :=
begin
  split,
  { intros h,
    have : b ∈ H.coset a,
    { rw h,
      exact H.gen_mem },
    rw H.mem_coset_iff ha at this,
    finish },
  { intros h,
    rw H.coset_eq_mul h,
    rw (show a * (b * a⁻¹) = b, by field_simp [ha]; ring) },
end

lemma coset_eq_of_mem {a b c : K} : a ∈ H.coset b → a ∈ H.coset c → H.coset b = H.coset c :=
begin
  intros ha hb,
  by_cases b = 0,
  { simp [h] at *,
    rw ha at hb,
    rw mem_zero_iff at hb,
    simp [hb] },
  rw coset_eq_iff _ h,
  rcases ha with ⟨x,hx,h1⟩,
  rcases hb with ⟨y,hy,h2⟩,
  rw h1 at h2,
  apply_fun (λ t, t * y⁻¹) at h2,
  simp [mul_assoc, H.mul_inv_cancel hy] at h2,
  rw ← h2,
  rw [mul_comm, ← mul_assoc, inv_mul_cancel h, one_mul],
  refine H.mul_mem hx (H.inv_mem hy),
end

lemma mem_coset_iff_mul_mem_coset {a b c : K} (h : a ∈ H) : b ∈ H.coset c ↔ a * b ∈ H.coset c :=
begin
  split,
  { rintro ⟨x,hx,rfl⟩,
    refine ⟨a * x, H.mul_mem h hx, by ring⟩ },
  { rintro ⟨x,hx,hh⟩,
    refine ⟨a⁻¹ * x,H.mul_mem (H.inv_mem h) hx, _⟩,
    field_simp [H.ne_zero h],
    finish },
end

@[simp] lemma coset_neg_eq_iff {a b : K} : H.coset (-a) = H.coset (-b) ↔ H.coset a = H.coset b :=
begin
  by_cases a = 0, { simp [h] },
  split,
  { intro h,
    rw coset_eq_iff at *,
    rwa (show -b * (-a)⁻¹ = b * a⁻¹, by simp [inv_neg]) at h,
    assumption,
    simpa },
  { intro h,
    rw coset_eq_iff at *,
    rwa (show -b * (-a)⁻¹ = b * a⁻¹, by simp [inv_neg]),
    simpa,
    assumption },
end

end mult_subgroup
