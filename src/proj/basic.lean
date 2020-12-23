import linear_algebra

variables (k : Type*) [field k] (V : Type*) [add_comm_group V] [vector_space k V]
def nonzero_vectors := {v : V // v ≠ 0}
variables {k V}

namespace nonzero_vectors
instance : has_coe (nonzero_vectors V) V := ⟨λ v, v.1⟩
end nonzero_vectors

lemma ne_zero_of_smul {v : V} {a : k} {w : nonzero_vectors V} : a • v = w.1 → a ≠ 0 := sorry

namespace proj

variables (k V)

def setoid : setoid (nonzero_vectors V) :=
{ r := λ v w, ∃ a : k, a • (v : V) = (w : V),
  iseqv := begin
    refine ⟨λ v, _,λ v w, _,λ u v w, _⟩,
    { use 1, simp, },
    { rintro ⟨a,ha⟩,
      use a⁻¹,
      rw [← ha, ← mul_smul, inv_mul_cancel (ne_zero_of_smul ha), one_smul] },
    { rintro ⟨a,ha⟩ ⟨b,hb⟩,
      use b * a,
      simp only [mul_smul, ha, hb] },
  end }

end proj

variables (k V)
def proj := quotient (proj.setoid k V)

namespace proj

variables {k V}
def mk : nonzero_vectors V → proj k V := quotient.mk'
def mk' {v : V} (hv : v ≠ 0) : proj k V := quotient.mk' ⟨v,hv⟩

variables (k V)
def emb : V → proj k (k × V) := λ v, proj.mk ⟨(1,v),by simp⟩

lemma emb.injective : function.injective (emb k V) :=
begin
  intros x y h,
  rcases (quotient.exact' h) with ⟨a,ha⟩,
  simp at ha,
  rcases ha with ⟨rfl,h⟩,
  simpa using h,
end

end proj
