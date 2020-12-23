import .preadd_of

open_locale classical

variables {K : Type*} [field K] (R : rig_pair K)

theorem exceptional_of_not_preadd (cond : ¬ preadd R) : R.T.exceptional :=
begin
  have : ∀ (a : K), a ≠ 0 → a ∉ R.T → R.T.rigid (-a),
  { intros a ha hh,
    by_contra c,
    have := R.preadd_of_nonrig ha hh c,
    finish },
  split,
  { intros x,
    by_cases hx : x = 0, {finish},
    right,
    intro hhx,
    by_contra c,
    simp [not_or_distrib] at c,
    cases c with c1 c2,
    apply hhx,
    split,
    rw (show x = - - x, by simp),
    refine this _ (by simpa) c2,
    refine this _ hx c1 },
  by_cases hno : (-1 : K) ∈ R.T, {finish},
  right,
  intros a b ha hb,
  specialize this (-1 : K) (by simp) hno a b ha hb,
  simpa using this,
end

lemma claim1_helper (a b : K) : a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → 1 - a * b ∈ R.T.coset (-a) :=
begin
  intros ha hb hT,
  have r1 := R.rigm ha.1 (1+a) (1+b) ha.2 hb.2,
  rw (show 1 + a + -a * (1 + b) = 1 - a * b, by ring) at r1,
  finish
end

lemma claim2_helper (a b : K) : a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → 1 - a * b ∈ R.T.coset (-b) :=
begin
  intros ha hb hT,
  have r2 := R.rigm hb.1 (1+b) (1+a) hb.2 ha.2,
  rw (show 1 + b + -b * (1 + a) = 1 - a * b, by ring) at r2,
  finish
end

lemma claim3_helper (a b : K) : a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → R.T.coset (-a) = R.T.coset (-b) :=
begin
  intros ha hb hT,
  refine R.T.coset_eq_of_mem (claim1_helper _ a b ha hb hT) (claim2_helper _ a b ha hb hT)
end

lemma claim4_helper (a b : K) : a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → R.T.coset a = R.T.coset b :=
begin
  intros ha hb hT,
  simpa using claim3_helper _ a b ha hb hT,
end

lemma hta_helper {a b : K} : a ≠ 0 → a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → (1 - a * b) * (-a)⁻¹ ∈ R.T :=
begin
  intros hanez ha hb hT,
  have := claim1_helper _ a b ha hb hT,
  rw R.T.mem_coset_iff at this,
  finish,
  simpa
end

lemma htb_helper {a b : K} : b ≠ 0 → a ∈ R.minus → b ∈ R.minus → 1 - a * b ∉ R.T → (1 - a * b) * (-b)⁻¹ ∈ R.T :=
begin
  intros hanez ha hb hT,
  have := claim2_helper _ a b ha hb hT,
  rw R.T.mem_coset_iff at this,
  finish,
  simpa
end

lemma rig_helper {a b : K} : a ≠ 0 → b ∉ R.H → (a * b ∈ R.T.coset 1 ∨ a * b ∈ R.T.coset a) → a * b ∈ R.T :=
begin
  intros hanez hbH hrig,
  cases hrig,
  simpa using hrig,
  exfalso,
  apply hbH,
  rw R.T.mem_coset_iff hanez at hrig,
  rw (show a⁻¹ * (a * b) = b, by field_simp [hanez]; ring) at hrig,
  refine R.incl hrig,
end

lemma mul_self_mem {a b : K} :
  a ∈ R.minus →
  b ∈ R.minus →
  1 - a * b ∉ R.T →
  a ≠ 0 →
  b ≠ 0 →
  a * b ∈ R.T →
  a * a ∈ R.T :=
begin
  intros ha hb hT hanez hbnez rig,
  have claim4 := claim4_helper _ a b ha hb hT,
  rw R.T.coset_eq_iff hanez at claim4,
  rw (show a * a = a * b * (b * a⁻¹)⁻¹, by field_simp [hanez, hbnez]; ring),
  refine R.T.mul_mem rig (R.T.inv_mem claim4)
end

lemma neg_mem_adjoin_helper {a : K} (hanez : a ≠ 0) : -a ∈ (R.adjoin hanez).H :=
begin
  rw (show -a = (-1) * a, by ring),
  exact mult_subgroup.mul_mem _ (rig_pair.neg_one_mem _) (mult_subgroup.adjoin_mem _ _),
end

lemma mem_adjoin_of_coset {a y : K} (hanez : a ≠ 0) : R.T.coset a = R.T.coset y → y ∈ (R.adjoin hanez).H :=
begin
  intro h,
  rw R.T.coset_eq_iff hanez at h,
  replace h := (R.adjoin hanez).incl h,
  rw (show y = y * a⁻¹ * a, by field_simp [hanez]),
  refine (R.H.adjoin hanez).mul_mem h _,
  apply mult_subgroup.adjoin_mem
end

theorem index_two : ∃ (x : K) (hx : x ≠ 0), x * x ∈ R.H ∧ (preadd (R.adjoin hx)) :=
begin
  by_cases pr : preadd R,
  { refine ⟨1,one_ne_zero,by simp [R.H.one_mem], by simpa⟩ },
  have exc := exceptional_of_not_preadd R pr,
  erw R.preadd_iff at pr,
  simp at pr,
  rcases pr with ⟨a,ha,b,hb,hT⟩,
  have hanez : a ≠ 0 := R.T.ne_zero_of_one_minus_mul_left hT,
  have hbnez : b ≠ 0 := R.T.ne_zero_of_one_minus_mul_right hT,
  let ta := (1-a*b) * (-a)⁻¹,
  let tb := (1-a*b) * (-b)⁻¹,
  have hta : ta ∈ R.T := hta_helper _ hanez ha hb hT,
  have htb : tb ∈ R.T := htb_helper _ hbnez ha hb hT,
  have hta2 : 1 - a * b = (-a) * ta,
  { dsimp [ta], rw [mul_comm (-a), mul_assoc, inv_neg, neg_mul_neg, inv_mul_cancel hanez, mul_one] },
  have htb2 : 1 - a * b = (-b) * tb,
  { dsimp [tb], rw [mul_comm (-b), mul_assoc, inv_neg, neg_mul_neg, inv_mul_cancel hbnez, mul_one] },
  have hab1 : a * b = 1 + a * ta,
  { apply_fun (λ t, t + a * b) at hta2, simp at hta2, rw [hta2, add_comm, ← add_assoc, add_neg_self, zero_add] },
  have hab2 : a * b = 1 + b * tb,
  { apply_fun (λ t, t + a * b) at htb2, simp at htb2, rw [htb2, add_comm, ← add_assoc, add_neg_self, zero_add] },
  have hab1_rig := R.rigp ha.1 1 ta R.T.one_mem hta,
  rw ← hab1 at hab1_rig,
  replace hab1_rig : a * b ∈ R.T := rig_helper _ hanez hb.1 hab1_rig,
  refine ⟨a,hanez,R.incl (mul_self_mem _ ha hb hT hanez hbnez hab1_rig), _⟩,
  suffices : -a ∈ (R.adjoin hanez).UU,
  { apply rig_pair.preadd_of_mem_UU_nmem_T _ this,
    change -a ∉ R.T,
    intro c,
    replace c := R.H.mul_mem (R.neg_one_mem) (R.incl c),
    finish [c, ha.1] },
  have neg_a_mem_adjoin : -a ∈ R.H.adjoin hanez := neg_mem_adjoin_helper _ _,
  refine ⟨⟨neg_a_mem_adjoin,_⟩,⟨mult_subgroup.inv_mem _ neg_a_mem_adjoin,_⟩⟩,
  { intros y hy,
    refine ⟨(R.H.adjoin hanez).mul_nmem_of_mem_nmem neg_a_mem_adjoin hy.1,_⟩,
    by_cases hynez : y = 0, { simp [hynez, mult_subgroup.one_mem] },
    by_contra contra,
    rw (show 1 + - a * y = 1 - a * y, by ring) at contra,
    have := claim4_helper _ a y ha _ contra,
    have coset_eq : y ∈ R.H.adjoin hanez := mem_adjoin_of_coset _ _ this,
    exact hy.1 coset_eq,
    exact rig_pair.minus_le _ hy },
  { intros y hy,
    by_cases hynez : y = 0,
    { simp [hynez], exact rig_pair.minus_zero_mem _ },
    by_contra contra,
    have nez : (-a)⁻¹ * y ≠ 0, { refine mul_ne_zero _ hynez, simpa },
    have := rig_pair.minus.mem_iff_inv_nmem (R.adjoin hanez) nez _,
    rw this at contra,
    simp [mul_inv'] at contra,
    have contra' : -(a * y⁻¹) ∈ R.minus := rig_pair.minus_le _ contra,
    have f1 := claim1_helper _ (-(a * y⁻¹)) (-(b * y)) contra' _ _,
    simp at f1,
    rw (show 1 - a * y⁻¹ * (b * y) = 1 - a * b, by field_simp [hynez]; ring) at f1,
    have f2 := claim1_helper _ a b ha hb hT,
    have f3 := R.T.coset_eq_of_mem f1 f2,
    rw R.T.coset_eq_iff at f3,
    rw (show -a * (a * y⁻¹)⁻¹ = -y, by field_simp [hanez]; ring) at f3,
    refine hy.1 _,
    refine (R.adjoin hanez).H.mem_of_mul_mem_mem_right (_ : (-1 : K) * y ∈ _) (R.adjoin hanez).neg_one_mem,
    refine (R.adjoin hanez).incl _,
    simpa,
    refine mul_ne_zero hanez (by simpa),
    { refine ⟨_,_⟩,
      have : a * b⁻¹ ∈ R.H,
      { have claim4 := claim4_helper _ b a hb ha _,
        rw R.T.coset_eq_iff hbnez at claim4,
        exact R.incl claim4,
        rwa mul_comm },
      intro cc,
      have := R.H.mul_mem this cc,
      rw (show a * b⁻¹ * -(b * y) = -(a * y), by field_simp [hbnez]; ring) at this,
      have := R.H.mul_nmem_of_mem_nmem this contra'.1,
      rw (show -(a * y) * -(a * y⁻¹) = a * a, by field_simp [hynez]; ring) at this,
      apply this,
      refine R.incl _,
      have claim4 := claim4_helper _ a b ha hb hT,
      rw R.T.coset_eq_iff hanez at claim4,
      rw (show a * a = a * b * (b * a⁻¹)⁻¹, by field_simp [hanez, hbnez]; ring),
      refine R.T.mul_mem hab1_rig (R.T.inv_mem claim4),
      rw (show 1 + - (b * y) = 1 - b * y, by ring),
      by_contra contra'',
      have claim4 := claim4_helper _ b y hb _ contra'',
      rw R.T.coset_eq_iff at claim4,
      replace claim4 := R.T.mul_mem claim4 hab1_rig,
      rw (show y * b⁻¹ * (a * b) = y * a, by field_simp [hbnez]; ring) at claim4,
      replace claim4 := (R.adjoin hanez).incl claim4,
      apply contra.1,
      refine (R.H.adjoin hanez).mem_of_mul_mem_mem_right _ claim4,
      rw (show y * a * -(a * y⁻¹) = (-1) * (a * a), by field_simp [hynez]; ring),
      refine (R.adjoin hanez).H.mul_mem (R.adjoin hanez).neg_one_mem _,
      refine (R.adjoin hanez).incl _,
      have claim4' := claim4_helper _ a b ha hb hT,
      rw R.T.coset_eq_iff hanez at claim4',
      rw (show a * a = a * b * (b * a⁻¹)⁻¹, by field_simp [hanez, hbnez]; ring),
      refine R.T.mul_mem hab1_rig (R.T.inv_mem claim4'),
      exact hbnez,
      refine rig_pair.minus_le _ hy },
    rwa (show 1 - -(a * y⁻¹) * -(b * y) = 1 - a * b, by field_simp [hynez]; ring),
    refine (R.adjoin hanez).H.mul_nmem_of_mem_nmem _ _,
    refine (R.adjoin hanez).H.inv_mem _,
    rw (show -a = (-1) * a, by ring),
    refine (R.adjoin hanez).H.mul_mem _ _,
    exact (R.adjoin hanez).neg_one_mem,
    apply mult_subgroup.adjoin_mem,
    exact hy.1 },
end
