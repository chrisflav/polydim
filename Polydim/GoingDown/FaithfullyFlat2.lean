import Mathlib.RingTheory.Flat.FaithfullyFlat
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.RingHom.Flat

open LinearMap LocalizedModule

variable {R S : Type*} [CommRing R] [CommRing S]

theorem a1 [Algebra R S] [Module.Flat R S]
    (h : ∀ (m : Ideal R) (_ : m.IsMaximal), ∃ m' : Ideal S, m'.IsMaximal ∧ m'.LiesOver m) :
    Module.FaithfullyFlat R S := by
  constructor
  intro m hm
  obtain ⟨m', hm', H⟩ := h m hm
  rw [Ideal.smul_top_eq_map, H.over.trans (m'.under_def R)]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    fun top ↦ hm'.ne_top <| top_le_iff.mp <| top ▸ Ideal.map_comap_le

def RingHom.FaithfullyFlat (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

lemma a2 [IsLocalRing R] [IsLocalRing S] (f : R →+* S)
    (hl : IsLocalHom f) (hf : f.Flat) : f.FaithfullyFlat := by
  algebraize [f]
  have h := ((IsLocalRing.local_hom_TFAE f).out 0 4).mp hl
  exact a1 fun m hm ↦ ⟨IsLocalRing.maximalIdeal S,
    ⟨IsLocalRing.maximalIdeal.isMaximal S, ⟨(IsLocalRing.eq_maximalIdeal hm).symm ▸ h.symm⟩⟩⟩

open TensorProduct

lemma Module.FaithfullyFlat.instTensorProduct (R S M N: Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S M]
    [IsScalarTower R S M] [FaithfullyFlat S M] [FaithfullyFlat R N] :
    FaithfullyFlat S (M ⊗[R] N) :=
  (Module.FaithfullyFlat.iff_flat_and_lTensor_faithful S (M ⊗[R] N)).mpr ⟨Flat.instTensorProduct,
    fun L _ _ _ ↦ letI : Nontrivial ((M ⊗[S] L) ⊗[R] N) := rTensor_nontrivial R N (M ⊗[S] L);
      (TensorProduct.AlgebraTensorModule.rightComm R S M L N).injective.nontrivial⟩

instance Module.FaithfullyFlat.baseChange (R S M : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [FaithfullyFlat R M] : FaithfullyFlat S (S ⊗[R] M) := by
  exact instTensorProduct R S S M

theorem Module.FaithfullyFlat.isBaseChange (R S M N: Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [FaithfullyFlat R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) : FaithfullyFlat S N :=
  of_linearEquiv S (S ⊗[R] M) (IsBaseChange.equiv h).symm

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
variable {M N : Type*}
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

private lemma invpair (f : M ≃ₗ[R] N) (g : N ≃ₗ[R] M) (h : ∀ x, f (g x) = x) :
    f.extendScalarsOfIsLocalization S A ∘ₗ g.extendScalarsOfIsLocalization S A = .id := by
  ext x
  simp only [coe_comp, Function.comp_apply,
    extendScalarsOfIsLocalization_apply', LinearEquiv.coe_coe, id_coe, id_eq, h x]

def LinearEquiv.extendScalarsOfIsLocalization (f : M ≃ₗ[R] N) : M ≃ₗ[A] N := LinearEquiv.ofLinear
  (f.1.extendScalarsOfIsLocalization S A) (f.symm.1.extendScalarsOfIsLocalization S A)
  (invpair _ _ f f.symm <| fun x ↦ apply_symm_apply f x)
  (invpair _ _ f.symm f <| fun x ↦ symm_apply_apply f x)

end

lemma Module.FaithfullyFlat.a3 (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] (p : Ideal R)
    (hp : p.IsPrime) : ∃ p' : Ideal S, p'.IsPrime ∧ p'.LiesOver p := by
  set Rp := Localization p.primeCompl
  set Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI := localizationAlgebra p.primeCompl S (Rₘ := Rp) (Sₘ := Sp)
  letI : IsScalarTower R Rp Sp := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  letI : IsLocalizedModule p.primeCompl (Algebra.linearMap S Sp) (M := S) (M' := Sp) :=
    (isLocalizedModule_iff_isLocalization).mpr Localization.isLocalization
  set g1 := IsLocalizedModule.iso p.primeCompl ((Algebra.linearMap S Sp).restrictScalars R)
  set g2 := LinearEquiv.extendScalarsOfIsLocalization p.primeCompl Rp g1
  set g3 := (IsLocalizedModule.isBaseChange p.primeCompl Rp (mkLinearMap p.primeCompl S)).equiv
  have h2 := IsLocalization.AtPrime.comap_maximalIdeal (Localization p.primeCompl) p
  set q := IsLocalRing.maximalIdeal (Localization p.primeCompl)
  have maxq : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal (Localization p.primeCompl)
  have n := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal _ _).mp (of_linearEquiv Rp _ (g3 ≪≫ₗ g2).symm)).2 q Ideal.IsPrime.ne_top'
  rw [Ideal.smul_top_eq_map, (Submodule.restrictScalars_eq_top_iff _ _ _).ne] at n
  set q' := q.map (algebraMap (Localization p.primeCompl) Sp)
  obtain ⟨m, maxm, hm⟩ := q'.exists_le_maximal n
  have h4 : q = m.under Rp := Ideal.IsMaximal.eq_of_le maxq Ideal.IsPrime.ne_top'
    (Ideal.le_comap_of_map_le hm)
  set p' := m.comap (algebraMap S Sp)
  exact ⟨p', Ideal.IsPrime.under S m, ⟨(m.under_under (A := R) (B := S)) ▸
    (m.under_under (A := R) (B := Rp)).symm ▸  h4.symm ▸ h2.symm⟩⟩
