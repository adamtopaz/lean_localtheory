import .coset
import .adjoin
import ..helpers

open_locale classical

variables {K : Type*} [field K] (H : mult_subgroup K)

namespace mult_subgroup

def rigid (x : K) : Prop := ∀ (h0 h1 : K), h0 ∈ H → h1 ∈ H →
  h0 + x * h1 ∈ H.coset 1 ∨ h0 + x * h1 ∈ H.coset x

lemma rigid_zero : H.rigid 0 :=
begin
  intros u v hu hv,
  left,
  simpa,
end

def birigid (x : K) : Prop := H.rigid x ∧ H.rigid (-x)

lemma birigid_zero : H.birigid 0 := by simp [birigid, rigid_zero]

def exceptional : Prop :=
(∀ x : K, x = 0 ∨ ((¬ H.birigid x) → (x ∈ H ∨ -x ∈ H))) ∧
((-1 : K) ∈ H ∨ (∀ a b : K, a ∈ H → b ∈ H → a + b ∈ H))

lemma zero_rigid : H.rigid 0 := λ h0 h1 hh0 hh1, or.inl $ by simpa
lemma zero_birigid : H.birigid 0 := ⟨H.zero_rigid, by {simp , exact H.zero_rigid}⟩

lemma mul_rigid {x h : K} : h ∈ H → H.rigid x → H.rigid (x * h) :=
begin
  intros h0 h1 a b ha hb,
  cases h1 a (b * h) ha (H.mul_mem hb h0) with h2 h2,
  finish,
  right,
  rw H.coset_eq_mul h0 at h2,
  finish,
end

end mult_subgroup

variable (K)
@[ext]
structure rig_pair :=
(T : mult_subgroup K)
(H : mult_subgroup K)
(incl : T ≤ H)
(birig {x : K} : x ∉ H → T.birigid x)

namespace rig_pair

variables {K} (R : rig_pair K)

def rigp {x : K} (hx : x ∉ R.H) : R.T.rigid x := (R.birig hx).1
def rigm {x : K} (hx : x ∉ R.H) : R.T.rigid (-x) := (R.birig hx).2

lemma neg_one_mem : (-1 : K) ∈ R.H :=
begin
  by_contra c,
  cases R.rigp c 1 1 R.T.one_mem R.T.one_mem,
  { simp at h,
    change _ ∈ R.T at h,
    finish [R.T.zero_nmem] },
  { simp [R.T.mem_coset_iff] at h,
    finish [R.T.zero_nmem] }
end

lemma neg_mem_of_mem {x : K} : x ∈ R.H → -x ∈ R.H :=
begin
  intro h,
  rw (show -x = (-1) * x, by ring),
  exact R.H.mul_mem R.neg_one_mem h,
end

def minus : set K := {x | x ∉ R.H ∧ 1 + x ∈ R.T}
def plus : set K := {x | x ∈ R.H ∧ (∀ y : K, y ∈ R.minus → x * y ∈ R.minus)}
def OO : set K := R.minus ∪ R.plus
def UU : set K := {x | x ∈ R.plus ∧ x⁻¹ ∈ R.plus}

-- 2.3 1
lemma plus_one_mem : (1 : K) ∈ R.plus := ⟨R.H.one_mem, λ y hy, by simpa⟩

-- 2.3 1
lemma plus_mul_mem {x y : K} : x ∈ R.plus → y ∈ R.plus → x * y ∈ R.plus :=
begin
  intros hx hy,
  refine ⟨R.H.mul_mem hx.1 hy.1, λ z hz, _⟩,
  rw mul_assoc,
  exact hx.2 _ (hy.2 _ hz),
end

-- 2.3 2
lemma minus_zero_mem : (0 : K) ∈ R.minus := ⟨R.H.zero_nmem , by finish [R.T.one_mem]⟩

lemma zero_mem : (0 : K) ∈ R.OO := or.inl R.minus_zero_mem

-- help for 2.3 3 statement about cosets
lemma nmem_of_nmem {x : K} : x ∉ R.H → x ∉ R.T := λ h c, h $ R.incl c

lemma minus.ne_neg_one {x : K} : x ∈ R.minus → x ≠ -1 := λ h c, R.T.zero_nmem $ by simpa [c] using h.2

lemma minus.mem_iff_inv_nmem {x : K} (hx : x ≠ 0) (hH : x ∉ R.H) :
  x ∈ R.minus ↔ x⁻¹ ∉ R.minus :=
begin
  split,
  { intro h,
    simp [minus],
    rintro -,
    cases R.rigp hH 1 1 R.T.one_mem R.T.one_mem with h1 h1,
    { simp at h1,
      have : 1 + x⁻¹ ∈ R.T.coset (x⁻¹),
      { rw R.T.mem_coset_iff,
        convert h.2,
        field_simp [hx],
        ring,
        simpa },
      apply R.T.coset_nmem_of_mem (R.T.inv_nmem (nmem_of_nmem _ hH)) this },
    { rw R.T.mem_coset_iff hx at h1,
      simp at h1,
      have := R.H.mem_of_inv_mem (R.incl (R.T.mem_of_mul_mem_mem_left h1 h.2)),
      finish } },
  { intro h,
    refine ⟨hH,_⟩,
    erw not_and_distrib at h,
    cases h,
    { finish [R.H.inv_nmem hH] },
    cases R.rigp hH 1 1 R.T.one_mem R.T.one_mem with h1 h1,
    simpa using h1,
    rw R.T.mem_coset_iff hx at h1,
    rw (show x⁻¹ * (1 + x * 1) = 1 + x⁻¹, by field_simp [hx]; ring) at h1,
    finish },
end

-- 2.3 4
lemma inv_mem_minus_mul_minus {x : K} : x ∈ R.H → x ∉ R.plus → ∃ (y z : K),
  y ∈ R.minus ∧ z ∈ R.minus ∧ x⁻¹ = y * z :=
begin
  intros hx hp,
  erw not_and_distrib at hp,
  cases hp,
  finish [R.H.ne_zero hx],
  simp at hp,
  rcases hp with ⟨y,hy1,hy2⟩,
  have hy : y ≠ 0,
  { intro c,
    simp [c] at hy2,
    finish [minus_zero_mem] },
  refine ⟨y,(x * y)⁻¹,hy1, _, _⟩,
  rw minus.mem_iff_inv_nmem,
  simpa,
  apply inv_ne_zero,
  refine mul_ne_zero (R.H.ne_zero hx) hy,
  apply R.H.inv_nmem,
  refine R.H.mul_nmem_of_mem_nmem hx hy1.1,
  rw [mul_comm x, mul_inv', ← mul_assoc, mul_inv_cancel hy, one_mul],
end

-- 2.3 5
lemma rigtrans_mem {x : K} : x ∈ R.minus → rigtrans x ∈ R.minus :=
begin
  rintro ⟨h1,h2⟩,
  split,
  refine R.H.mul_nmem_of_nmem_mem _ (R.H.inv_mem $ R.incl h2),
  intro c,
  replace c := R.neg_mem_of_mem c,
  finish,
  have : x ≠ -1,
  { rw ne_neg_one_iff,
    exact R.T.ne_zero h2 },
  rw (show 1 + rigtrans x = (1 + x)⁻¹, by field_simp [ne_neg_one_iff.mp this]),
  exact R.T.inv_mem h2,
end

def extend {H' : mult_subgroup K} (inc : R.H ≤ H') : rig_pair K :=
{ T := R.T,
  H := H',
  incl := mult_subgroup.le_trans R.incl inc,
  birig := λ x hx, R.birig $ λ c, hx $ inc c }

@[simp] lemma extend_T {H' : mult_subgroup K} {inc : R.H ≤ H'} : (R.extend inc).T = R.T := rfl
@[simp] lemma extend_H {H' : mult_subgroup K} {inc : R.H ≤ H'} : (R.extend inc).H = H' := rfl

@[simp] def adjoin {x : K} (hx : x ≠ 0) : rig_pair K := R.extend (R.H.le_adjoin hx)

@[simp] lemma adjoin_one : R.adjoin one_ne_zero = R := by {ext1, refl, simp}

end rig_pair
