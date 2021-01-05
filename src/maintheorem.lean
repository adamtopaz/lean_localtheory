import .mult_subgroup.indextwo
import .val_subring
import .mult_subgroup.to_val

variables (K : Type*) [field K] (T H : mult_subgroup K)
variables (incl : T ≤ H)
variables (cond0 : (-1 : K) ∈ T)
variables (cond1 : ∀ x : K, x ∉ H → 1 - x ∈ T ∨ 1 - x ∈ T.coset x)

include incl cond0 cond1

theorem maintheorem : ∃ (R : val_subring K) {x : K} (hx : x ≠ 0),
  x * x ∈ H ∧ R.units ⊆ (H.adjoin hx) ∧ R.principal_units ⊆ T :=
begin
  let RP : rig_pair K := ⟨T, H, incl, _⟩,
  rcases index_two RP with ⟨x,hx,h1,h2⟩, -- Key I: indextwo.lean
  let R := to_val (RP.adjoin hx) h2, -- Key II: to_val.lean
  refine ⟨R,x,hx,h1,_,_⟩,
  exact rig_pair.units_sub _,
  exact rig_pair.principal_units_sub _,
  intros x hx,
  by_cases hhx : x = 0,
  {simp [hhx, T.birigid_zero]},
  split,
  { intros u v hu hv,
    cases cond1 (x * (-v/u)) _,
    { left,
      simp,
      convert T.mul_mem hu h,
      field_simp [T.ne_zero hu],
      ring },
    { right,
      rw ← T.coset_eq_mul (_ : (-v/u) ∈ T) at h,
      rw T.mem_coset_iff hhx,
      rw T.mem_coset_iff hhx at h,
      field_simp at *,
      convert T.mul_mem hu h,
      field_simp [hhx, T.ne_zero hu],
      ring,
      rw (show -v / u = (-1) * v * u⁻¹, by field_simp [T.ne_zero hu]),
      refine T.mul_mem (T.mul_mem cond0 hv) (T.inv_mem hu) },
    refine H.mul_nmem_of_nmem_mem hx (incl _),
    rw (show -v / u = (-1) * v * u⁻¹, by field_simp [T.ne_zero hu]),
    refine T.mul_mem (T.mul_mem cond0 hv) (T.inv_mem hu) },
  { intros u v hu hv,
    cases cond1 (x * (v/u)) _,
    { left,
      simp,
      convert T.mul_mem hu h,
      field_simp [T.ne_zero hu],
      ring },
    { right,
      rw ← T.coset_eq_mul (_ : (v / u) ∈ T) at h,
      rw [(show -x = (-1) * x, by simp), T.coset_eq_mul cond0],
      simp,
      rw T.mem_coset_iff hhx,
      rw T.mem_coset_iff hhx at h,
      field_simp at *,
      convert T.mul_mem hu h,
      field_simp [hhx, T.ne_zero hu],
      ring,
      rw (show v / u = v * u⁻¹, by field_simp),
      refine T.mul_mem hv (T.inv_mem hu) },
    refine H.mul_nmem_of_nmem_mem hx (incl _),
    rw (show v / u = v * u⁻¹, by field_simp),
    refine T.mul_mem hv (T.inv_mem hu) }
end
