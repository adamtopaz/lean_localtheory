import ..val_subring
import .preadd

variables {K : Type*} [field K] (R : rig_pair K)

namespace rig_pair

lemma val_one_mem (pr : preadd R) : (1 : K) ∈ R.OO := or.inr R.plus_one_mem

lemma val_zero_mem (pr : preadd R) : (0 : K) ∈ R.OO := or.inl R.minus_zero_mem

lemma val_mul_mem {x y : K} (pr : preadd R) : x ∈ R.OO → y ∈ R.OO → x * y ∈ R.OO :=
begin
  rintro (hx|hx) (hy|hy),
  { by_cases x * y ∈ R.H,
    { exact or.inr (R.mem_plus_of_preadd pr hx hy h) },
    left,
    refine ⟨h,_⟩,
    have := (R.plus_neg_one_mem pr).2 _ hx,
    rw preadd_iff at pr,
    convert pr _ _ this hy,
    ring },
  { left,
    rw mul_comm,
    exact hy.2 _ hx },
  { left,
    exact hx.2 _ hy },
  { right,
    refine R.plus_mul_mem hx hy },
end

lemma val_one_plus {x : K} (pr : preadd R) : x ∈ R.OO → 1 + x ∈ R.OO :=
begin
  rintro (h|h),
  { exact or.inr (pr _ h) },
  { by_cases c1 : x = -1,
    { finish [c1, val_zero_mem] },
    have hox : (1+x) ≠ 0, by rwa ← ne_neg_one_iff,
    have hnox : -(1+x) ≠ 0, by rwa neg_ne_zero,
    by_cases c2 : x = 0,
    { finish [c2, val_one_mem] },
    have claim : 1 - (1 + x) ∈ R.plus,
    { refine ⟨_, λ y hy, _⟩,
      rw (show 1 - (1 + x) = (-1) * x, by ring),
      refine R.H.mul_mem R.neg_one_mem h.1,
      rw (show (1 - (1 + x)) * y = (-1) * (x * y), by ring),
      exact (R.plus_neg_one_mem pr).2 _ (h.2 _ hy) },
    have : ∀ (y : K), y ∈ R.minus → 1 + (1 + x) * y ∈ R.T ∧ 1 + (1 + x) * y ∈ R.plus,
    { intros y hy,
      rw (show 1 - (1 + x) = 1 + -(1 + x), by ring) at claim,
      have := R.mem_inter_of_preadd pr hnox claim hy,
      rw (show 1 - -(1+x) * y = 1 + (1 + x) * y, by ring) at this,
      exact this },
    by_cases c3 : 1 + x ∈ R.H,
    { refine or.inr ⟨c3, λ y hy, ⟨R.H.mul_nmem_of_mem_nmem c3 hy.1, _⟩⟩,
      exact (this y hy).1 },
    suffices : -(1+x) ∈ R.minus,
    { left,
      convert (R.plus_neg_one_mem pr).2 _ this,
      ring },
    have hnpxH : -(1+x) ∉ R.H,
    { rw (show -(1+x) = (-1) * (1 + x), by ring),
      exact R.H.mul_nmem_of_mem_nmem R.neg_one_mem c3 },
    rw minus.mem_iff_inv_nmem R hnox hnpxH,
    intro c,
    have cc := (this _ c).1,
    have : 1 + (1 + x) * (-(1+x))⁻¹ = 0,
    { simp only [inv_neg, ← neg_mul_eq_mul_neg], field_simp [hox] },
    rw this at cc,
    finish [R.T.zero_nmem] },
end

lemma val_cond {x : K} (pr : preadd R) : x ∈ R.OO ∨ x⁻¹ ∈ R.OO :=
begin
  by_cases h : x ∈ R.OO,
  { exact or.inl h },
  { refine or.inr (R.inv_mem_of_nmem pr h), }
end

lemma val_add_mem {x y : K} (pr : preadd R) : x ∈ R.OO → y ∈ R.OO → x + y ∈ R.OO :=
begin
  intros hx hy,
  by_cases hxz : x = 0, {simpa [hxz]},
  by_cases hyz : y = 0, {simpa [hyz]},
  by_cases x * y⁻¹ ∈ R.OO,
  { rw (show x + y = y * (1 + x * y⁻¹), by field_simp; ring),
    refine R.val_mul_mem pr hy (R.val_one_plus pr h) },
  rw (show x + y = x * (1 + (x * y⁻¹)⁻¹), by field_simp; ring),
  replace h := R.inv_mem_of_nmem pr h,
  refine R.val_mul_mem pr hx (R.val_one_plus pr h),
end

lemma val_neg_mem {x : K} (pr : preadd R) : x ∈ R.OO → -x ∈ R.OO :=
begin
  intro hx,
  rw (show -x = (-1) * x, by ring),
  exact R.val_mul_mem pr (or.inr (R.plus_neg_one_mem pr)) hx,
end

end rig_pair

def to_val (pr : preadd R) : val_subring K :=
{ carrier := R.OO,
  one_mem' := R.val_one_mem pr,
  mul_mem' := λ a b, R.val_mul_mem pr,
  zero_mem' := R.val_zero_mem pr,
  add_mem' := λ a b, R.val_add_mem pr,
  neg_mem' := λ a, R.val_neg_mem pr,
  val_cond := λ a, R.val_cond pr }

namespace rig_pair

lemma units_eq {pr : preadd R} : (to_val _ pr).units = R.UU :=
begin
  ext,
  split,
  { rintro ⟨h1,h2|h2,h3|h3⟩,
    all_goals {split},
    any_goals {assumption},
    any_goals {finish [minus.mem_iff_inv_nmem R h1 h2.1]},
    all_goals {exfalso},
    exact h2.1 (R.H.mem_of_inv_mem h3.1),
    exact h3.1 (R.H.inv_mem h2.1) },
  { rintro ⟨h1,h2⟩,
    exact ⟨R.H.ne_zero h1.1, or.inr h1, or.inr h2⟩ },
end

lemma units_sub {pr : preadd R} : (to_val _ pr).units ⊆ R.H :=
begin
  rintros x ⟨h1,h2|h2,h3|h3⟩,
  any_goals {exact h2.1},
  { finish [minus.mem_iff_inv_nmem R h1 h2.1] },
  { refine R.H.mem_of_inv_mem h3.1 }
end

lemma minus_sub {pr : preadd R} : R.minus ⊆ (to_val _ pr).maximal_ideal :=
begin
  rintros x hx,
  refine ⟨or.inl hx, λ c, _⟩,
  rcases c with ⟨c1,c2|c2,c3|c3⟩,
  finish [(minus.mem_iff_inv_nmem R c1 c2.1).mp c2],
  any_goals {exact hx.1 (R.H.mem_of_inv_mem c3.1)},
  exact hx.1 c2.1,
end

lemma principal_units_sub {pr : preadd R} : (to_val _ pr).principal_units ⊆ R.T :=
begin
  rintros x ⟨⟨_,h1⟩|h1,h2⟩,
  simpa using h1,
  rw R.units_eq at h2,
  simp at h2,
  erw not_and_distrib at h2,
  cases h2,
  { finish },
  rcases R.inv_mem_minus_mul_minus (R.H.inv_mem h1.1) h2 with ⟨u,v,h1,h2,h3⟩,
  simp at h3,
  rw (show x = 1 + u * v, by rw ← h3; ring),
  have : (-1) * u ∈ R.minus := (R.plus_neg_one_mem pr).2 _ h1,
  rw (show 1 + u * v = 1 - ((-1) * u * v), by ring),
  rw preadd_iff at pr,
  exact pr _ _ this h2,
end

end rig_pair
