import .rigid

open_locale classical

variables {K : Type*} [field K] (R : rig_pair K)

def preadd := ∀ (x : K), x ∈ R.minus → 1 + x ∈ R.plus

namespace rig_pair

lemma preadd_iff_0 : preadd R ↔ (∀ x z : K, x ∈ R.minus → z ∈ R.minus → 1 + (1 + x) * z ∈ R.T) :=
iff.intro (λ h x z hx hz, ((h x hx).2 z hz).2)
(λ h x hx, ⟨R.incl hx.2, λ y hy, ⟨R.H.mul_nmem_of_mem_nmem (R.incl hx.2) hy.1, h _ _ hx hy⟩⟩)

lemma preadd_iff_1 : preadd R ↔ (∀ x y : K, x ∈ R.minus → y ∈ R.minus → 1 + (1 + x) * rigtrans y ∈ R.T) :=
begin
  rw preadd_iff_0,
  split,
  { intros h x y hx hy,
    exact h x (rigtrans y) hx (R.rigtrans_mem hy) },
  { intros h x z hx hz,
    have := minus.ne_neg_one _ hz,
    rw ← rigtrans_rigtrans this,
    refine h _ _ hx (R.rigtrans_mem hz) },
end

-- 2.6 1 <-> 2
theorem preadd_iff : preadd R ↔ (∀ x y : K, x ∈ R.minus → y ∈ R.minus → 1 - x * y ∈ R.T) :=
begin
  rw preadd_iff_1,
  split,
  { intros h x y hx hy,
    have : 1 - x * y = (1 + y) * (1 + (1 + x) * rigtrans y),
    { field_simp [ne_neg_one_iff.mp (minus.ne_neg_one _ hy)],
      ring },
    rw this,
    refine R.T.mul_mem hy.2 _,
    apply h _ _ hx hy },
  { intros h x y hx hy,
    have : 1 - x * y = (1 + y) * (1 + (1 + x) * rigtrans y),
    { field_simp [ne_neg_one_iff.mp (minus.ne_neg_one _ hy)],
      ring },
    specialize h x y hx hy,
    rw this at h,
    refine R.T.mem_of_mul_mem_mem_right h hy.2 }
end

-- 2.6 3
lemma mem_inter_of_preadd {x y : K} : preadd R → x ≠ 0 → 1 + x ∈ R.plus → y ∈ R.minus →
  1 - x * y ∈ R.T ∧ 1 - x * y ∈ R.plus :=
begin
  intros cond hx hxp hy,
  have claim := hxp.2 (rigtrans y) (R.rigtrans_mem hy),
  have : 1 - x * y = (1 + y) * (1 + (1 + x) * rigtrans y),
  { field_simp [ne_neg_one_iff.mp (minus.ne_neg_one _ hy)],
    ring },
  rw this,
  exact ⟨R.T.mul_mem hy.2 claim.2, plus_mul_mem _ (cond _ hy) (cond _ claim)⟩,
end

-- 2.9 1
lemma mem_plus_of_preadd {x y : K} (pr : preadd R) : x ∈ R.minus → y ∈ R.minus →
  x * y ∈ R.H → x * y ∈ R.plus :=
begin
  intros hx hy h,
  have hxz : x ≠ 0, by {intro c, simp [c] at h, finish [R.H.zero_nmem]},
  refine ⟨h, λ z hz, ⟨R.H.mul_nmem_of_mem_nmem h hz.1,_⟩⟩,
  cases R.mem_inter_of_preadd pr hxz (pr _ hx) hy with h1 h2,
  rw (show 1 - x * y = 1 + -(x * y), by ring) at h2,
  cases R.mem_inter_of_preadd pr (by simpa using R.H.ne_zero h) h2 hz with h3 h4,
  simpa using h3,
end

-- 2.9 2
lemma inv_mem_of_nmem {x : K} (pr : preadd R) : x ∉ R.OO → x⁻¹ ∈ R.OO :=
begin
  intro hx,
  have hxz : x ≠ 0, by {intro c, finish [c, R.zero_mem]},
  by_cases h : x ∈ R.H,
  { rcases R.inv_mem_minus_mul_minus h (by {unfold OO at hx, finish}) with ⟨y, z, hy, hz, h0⟩,
    rw h0,
    refine or.inr (R.mem_plus_of_preadd pr hy hz (h0 ▸ R.H.inv_mem h)) },
  { left,
    have : x⁻¹⁻¹ ∉ R.minus, by {unfold OO at hx, finish [hx]},
    rwa ← minus.mem_iff_inv_nmem R (by simpa : x⁻¹ ≠ 0) (R.H.inv_nmem h) at this },
end

-- 2.9 3
lemma plus_neg_one_mem (pr : preadd R) : (-1 : K) ∈ R.plus :=
begin
  by_contra c,
  suffices : (-1 : K) ∉ R.OO,
  { have := R.inv_mem_of_nmem pr this,
    rw (show (-1 : K)⁻¹ = -1, by field_simp) at this,
    finish },
  simp [OO, not_or_distrib],
  refine ⟨_, c⟩,
  simp [minus],
  intro cc,
  finish [R.neg_one_mem]
end


lemma minus_le {H' : mult_subgroup K} {inc : R.H ≤ H'} : (R.extend inc).minus ⊆ R.minus :=
  λ x hx, ⟨λ c, hx.1 $ inc c, hx.2⟩

lemma preadd_extend {H' : mult_subgroup K} {inc : R.H ≤ H'} (pr : preadd R) : preadd (R.extend inc) :=
begin
  rw preadd_iff at *,
  intros x y hx hy,
  exact pr _ _ (minus_le _ hx) (minus_le _ hy),
end

end rig_pair
