import linear_algebra

variables (k : Type*) [field k] (V : Type*) [add_comm_group V] [vector_space k V]

def nonzero_vectors := {v : V // v ≠ 0}

variables {k V}

namespace nonzero_vectors
instance : has_coe (nonzero_vectors V) V := ⟨λ v, v.1⟩
end nonzero_vectors

lemma ne_zero_of_smul {v : V} {a : k} {w : nonzero_vectors V} : a • v = w.1 → a ≠ 0 :=
λ ha c, by { simp [c] at ha, exact w.2 ha.symm }

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

variables {k V}

end proj

variables (k V)
def proj := quotient (proj.setoid k V)
variables {k V}

namespace proj

def mk : nonzero_vectors V → proj k V := quotient.mk'
def mk' {v : V} (hv : v ≠ 0) : proj k V := quotient.mk' ⟨v,hv⟩

variables (k V)
def emb : V → proj k (k × V) := λ v, proj.mk ⟨(1,v),by simp⟩
variables {k V}

lemma emb.injective : function.injective (emb k V) :=
begin
  intros x y h,
  rcases (quotient.exact' h) with ⟨a,ha⟩,
  simp at ha,
  rcases ha with ⟨rfl,h⟩,
  simpa using h,
end

def map {W : Type*} [add_comm_group W] [vector_space k W] {f : V →ₗ[k] W} :
  function.injective f → proj k V → proj k W :=
λ hf x, quotient.lift_on' x (λ v, proj.mk ⟨f v, λ c,
  by {rw (show (0 : W) = f 0, by simp) at c, exact v.2 (hf c)}⟩)
begin
  rintros u v ⟨a,ha⟩,
  apply quotient.sound',
  use a,
  simp [← ha],
end

lemma map.injective {W : Type*} [add_comm_group W] [vector_space k W] {f : V →ₗ[k] W}
  {hf : function.injective f} : function.injective (map hf) :=
begin
  rintros ⟨x⟩ ⟨y⟩ h,
  apply quotient.sound',
  replace h := quotient.exact' h,
  rcases h with ⟨a,ha⟩,
  simp at ha,
  rw ← f.map_smul at ha,
  use a,
  exact hf ha,
end

end proj
