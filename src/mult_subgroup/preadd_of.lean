import .preadd

variables {K : Type*} [field K] (R : rig_pair K)

namespace rig_pair

lemma ne_zero_of_mem_UU {u : K} : u ∈ R.UU → u ≠ 0 := λ hu, R.H.ne_zero hu.1.1

-- 2.12
lemma preadd_of_mem_UU_nmem_T {u : K} : u ∈ R.UU → u ∉ R.T → preadd R :=
begin
  intros h1 h2,
  rw preadd_iff,
  intros x y hx hy,
  have claim1 := R.rigm hx.1 (1+x) (1+y) hx.2 hy.2,
  rw (show 1 + x + -x * (1 + y) = 1 - x * y, by ring) at claim1,
  have h0 := h1,
  cases h1 with h1 h3,
  have hhx := h3.2 _ hx,
  have hhy := h1.2 _ hy,
  have claim2 := R.rigm hhx.1 (1 + u⁻¹ * x) (1 + u * y) hhx.2 hhy.2,
  rw (show 1 + u⁻¹ * x + -(u⁻¹ * x) * (1 + u * y) = 1 - x * y, by field_simp [R.ne_zero_of_mem_UU h0]; ring)
    at claim2,
  cases claim1; cases claim2,
  any_goals {simpa using claim1 <|> simpa using claim2},
  have := R.T.coset_eq_of_mem claim1 claim2,
  have hx : x ≠ 0,
  { intros c,
    simpa [c] using claim1 },
  have hx' : -x ≠ 0, by simpa,
  rw R.T.coset_eq_iff hx' at this,
  rw (show -(u⁻¹ * x) * (-x)⁻¹ = u⁻¹, by field_simp [hx']) at this,
  refine false.elim (h2 $ R.T.mem_of_inv_mem this),
end

-- 2.13 -- Ware's Lemma
lemma mem_plus_of_nmem_nmem {u : K} : u ∈ R.H → u ∉ R.T → 1 - u⁻¹ ∉ R.T → u ∈ R.plus :=
begin
  intros h1 h2 h3,
  have hu : u ≠ 1,
  { intro c,
    simp [c] at h2,
    finish [R.T.one_mem] },
  have hu' : u-1 ≠ 0,
  { intros c,
    apply_fun (λ t, t + 1) at c,
    finish },
  have claim1 : u - 1 ∈ R.H,
  { by_contra c,
    have := R.rigp c 1 1 R.T.one_mem R.T.one_mem,
    simp at this,
    cases this,
    { finish },
    rw R.T.mem_coset_iff hu' at this,
    replace this := R.T.inv_mem this,
    rw (show ((u-1)⁻¹ * u)⁻¹ = 1 - u⁻¹, by field_simp [R.H.ne_zero h1]) at this,
    finish },
  refine ⟨h1,λ x hx, _⟩,
  have hxu : u * x ∉ R.H := R.H.mul_nmem_of_mem_nmem h1 hx.1,
  have hxu' : (u-1) * x ∉ R.H := R.H.mul_nmem_of_mem_nmem claim1 hx.1,
  have r1 := R.rigp hxu 1 1 R.T.one_mem R.T.one_mem,
  have r2 := R.rigp hxu' (1+x) 1 hx.2 R.T.one_mem,
  simp at r1,
  rw (show 1 + x + (u-1) * x * 1 = 1 + u * x, by ring) at r2,
  refine ⟨hxu,_⟩,
  cases r1; cases r2,
  any_goals {assumption <|> simpa using r2},
  have := R.T.coset_eq_of_mem r1 r2,
  by_cases hx : x = 0,
  { simp [hx, R.T.one_mem] },
  have huxnez : u * x ≠ 0 := mul_ne_zero (R.H.ne_zero h1) hx,
  rw R.T.coset_eq_iff huxnez at this,
  rw (show (u-1) * x * (u * x)⁻¹ = (u-1) *  u⁻¹, by field_simp [huxnez, hx, R.H.ne_zero h1]; ring) at this,
  rw (show (u-1) * u⁻¹ = 1 - u⁻¹, by field_simp [R.H.ne_zero h1]) at this,
  finish,
end

-- 2.14
lemma preadd_of_nonrig {a : K} : a ≠ 0 → a ∉ R.T → (¬R.T.rigid (-a)) → preadd R :=
begin
  intros ha haT hnr,
  have haH : a ∈ R.H,
  { by_contra c,
    finish [R.rigm c] },
  simp [mult_subgroup.rigid] at hnr,
  rcases hnr with ⟨t1,ht1,t2,ht2,htt⟩,
  rw not_or_distrib at htt,
  cases htt with htt1 htt2,
  let t := t2 * t1⁻¹,
  replace htt1 : 1 - a * t ∉ R.T,
  { rw (show 1 - a * t = t1⁻¹ * (t1 + -(a * t2)), by field_simp [t, R.T.ne_zero ht1]; ring),
    refine R.T.mul_nmem_of_mem_nmem (R.T.inv_mem ht1) htt1 },
  replace htt2 : 1 - a * t ∉ R.T.coset (-a),
  { rw (show 1 - a * t = t1⁻¹ * (t1 + -(a * t2)), by field_simp [t, R.T.ne_zero ht1]; ring),
    rwa ← R.T.mem_coset_iff_mul_mem_coset (R.T.inv_mem ht1) },
  have : t ∈ R.T := R.T.mul_mem ht2 (R.T.inv_mem ht1),
  rw (show R.T.coset (-a) = R.T.coset (-a * t), by rw R.T.coset_eq_mul this) at htt2,
  have hat : a * t ∉ R.T := R.T.mul_nmem_of_nmem_mem haT this,
  have hat' : a * t ∈ R.H := R.H.mul_mem haH (R.incl this),
  have hat'' : 1 - (a * t)⁻¹ ∉ R.T,
  { have : -a * t ≠ 0, by finish [R.H.ne_zero hat'],
    erw R.T.mem_coset_iff this at htt2,
    convert htt2,
    field_simp [R.H.ne_zero hat'],
    ring },
  have rr1 := R.mem_plus_of_nmem_nmem hat' hat hat'',
  have rr2 := R.mem_plus_of_nmem_nmem (R.H.inv_mem hat') (R.T.inv_nmem hat) (by simpa),
  exact R.preadd_of_mem_UU_nmem_T ⟨rr1,rr2⟩ hat
end

end rig_pair
