import .basic

variables {K : Type*} [field K] (H : mult_subgroup K)

namespace mult_subgroup

namespace adjoin
inductive aux {x : K} (hx : x ≠ 0) : K → Prop
| of {y : K} : y ∈ H → aux y
| const : aux x
| mul_mem {a b : K} : aux a → aux b → aux (a * b)
| inv_mem {a : K} : aux a → aux a⁻¹
end adjoin

def adjoin {x : K} (hx : x ≠ 0) : mult_subgroup K :=
{ carrier := adjoin.aux H hx,
  zero_nmem' := begin
    suffices : ∀ y : K, adjoin.aux H hx y → y ≠ 0,
    { intro c,
      exact this 0 c rfl },
    intros y hy,
    induction hy,
    case aux.of : y hy { exact H.ne_zero hy },
    case aux.const { assumption },
    case aux.mul_mem : a b ha hb hha hhb { exact mul_ne_zero hha hhb },
    case aux.inv_mem : a ha hha { exact inv_ne_zero hha },
  end,
  one_mem' := adjoin.aux.of $ H.one_mem,
  mul_mem' := λ a b ha hb, adjoin.aux.mul_mem ha hb,
  inv_mem' := λ a ha, adjoin.aux.inv_mem ha }

lemma le_adjoin {x : K} (hx : x ≠ 0) : H ≤ H.adjoin hx := λ x hx, adjoin.aux.of hx

lemma adjoin_mem {x : K} (hx : x ≠ 0) : x ∈ H.adjoin hx := adjoin.aux.const

lemma adjoin_le_of_mem {x : K} {H' : mult_subgroup K} (hx : x ≠ 0) (inc : H ≤ H') :
  x ∈ H' → H.adjoin hx ≤ H' :=
begin
  intros hx y hy,
  induction hy,
  case adjoin.aux.of : a ha { exact inc ha },
  case adjoin.aux.const { exact hx },
  case adjoin.aux.mul_mem : a b ha hb hha hhb { exact H'.mul_mem hha hhb },
  case adjoin.aux.inv_mem : a ha hha { exact H'.inv_mem hha },
end

@[simp] lemma adjoin_one : H.adjoin one_ne_zero = H :=
begin
  ext,
  split,
  { intro h,
    exact H.adjoin_le_of_mem one_ne_zero (by tauto) H.one_mem h },
  { intro h,
    refine le_adjoin _ _ h },
end

end mult_subgroup
