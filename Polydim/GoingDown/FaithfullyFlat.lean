import Mathlib
import Polydim.GoingDown.PrimeSpectrum

universe t s u v

lemma Function.Injective.iff_exact {R M N : Type*} (P : Type*) [Ring R]
    [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R N] [Module R M] [Module R P]
    (f : M →ₗ[R] N) :
    Function.Injective f ↔ Function.Exact (0 : P →ₗ[R] M) f := by
  simp [← LinearMap.ker_eq_bot, LinearMap.exact_iff]


section

variable {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

open TensorProduct LinearMap

lemma Module.FaithfullyFlat.injective_of_lTensor_injective [Module.FaithfullyFlat R M]
    {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') (hf : Function.Injective (lTensor M f)) :
    Function.Injective f := by
  rw [Function.Injective.iff_exact Unit]
  apply Module.FaithfullyFlat.lTensor_reflects_exact R M
  simpa only [lTensor_zero, ← Function.Injective.iff_exact]

end

section

variable {A : Type*} (B : Type v) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

private noncomputable def Algebra.TensorProduct.tensorQuotEquivQuotIdealMapAux (I : Ideal A) :
    TensorProduct A B (A ⧸ I) ≃ₗ[A] B ⧸ (I.map <| algebraMap A B) :=
  TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)

private lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMapAux_apply (b : B) (a : A) :
    tensorQuotEquivQuotIdealMapAux B I (b ⊗ₜ[A] a) =
      Submodule.Quotient.mk (a • b) :=
  rfl

private lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMapAux_symm_mk (b : B) :
    (tensorQuotEquivQuotIdealMapAux B I).symm
      (Ideal.Quotient.mk (I.map <| algebraMap A B) b) = b ⊗ₜ[A] 1 :=
  rfl

/-- `B ⊗[A] (A ⧸ I)` is isomorphic as an `A`-algebra to `B ⧸ I B`. -/
noncomputable def Algebra.TensorProduct.tensorQuotEquivQuotIdealMap :
    TensorProduct A B (A ⧸ I) ≃ₐ[A] B ⧸ (I.map <| algebraMap A B) :=
  AlgEquiv.ofLinearEquiv (tensorQuotEquivQuotIdealMapAux B I)
    (by
      rw [one_def, ← map_one (Ideal.Quotient.mk _), tensorQuotEquivQuotIdealMapAux_apply]
      simp)
    (fun x y ↦ (tensorQuotEquivQuotIdealMapAux B I).symm.injective <| by
      conv_lhs => rw [← (tensorQuotEquivQuotIdealMapAux B I).symm_apply_apply x,
        ← (tensorQuotEquivQuotIdealMapAux B I).symm_apply_apply y]
      induction' (tensorQuotEquivQuotIdealMapAux B I) x using Submodule.Quotient.induction_on with u
      induction' (tensorQuotEquivQuotIdealMapAux B I) y using Submodule.Quotient.induction_on with v
      simp only [LinearEquiv.symm_apply_apply, Ideal.Quotient.mk_eq_mk, ← map_mul,
        tensorQuotEquivQuotIdealMapAux_symm_mk, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one]
    )

@[simp]
lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMap_apply (b : B) (a : A) :
    tensorQuotEquivQuotIdealMap B I (b ⊗ₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

@[simp]
lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMap_symm_mk (b : B) :
    (tensorQuotEquivQuotIdealMap B I).symm b = b ⊗ₜ[A] 1 :=
  rfl

end

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open TensorProduct LinearMap

/-- If `M` is a `B`-module that is also an `A`-module, the canonical map
`M →ₗ[A] B ⊗[A] M` is injective. -/
lemma Module.tensorProduct_mk_injective_of_isScalarTower (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] : Function.Injective (TensorProduct.mk A B M 1) := by
  apply Function.RightInverse.injective (g := LinearMap.liftBaseChange B LinearMap.id)
  intro m
  simp

/-- If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective. -/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective [Module.FaithfullyFlat A B]
      (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  apply Module.FaithfullyFlat.injective_of_lTensor_injective B
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B ⊗[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
  exact Module.tensorProduct_mk_injective_of_isScalarTower _

/-- If `M →ₗ[A] B ⊗[A] M` is injective for every `A`-module `M`, `B` is a faithfully flat
`A`-algebra. -/
lemma Module.FaithfullyFlat.of_tensorProduct_mk_injective [Module.Flat A B]
    (h : ∀ (M : Type (max u v)) [AddCommGroup M] [Module A M], Function.Injective (TensorProduct.mk A B M 1)) :
    FaithfullyFlat A B := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ _ ↦ ?_⟩
  exact Function.Injective.nontrivial <| h N

/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      (AlgEquiv.toLinearMap (Algebra.TensorProduct.tensorQuotEquivQuotIdealMap B I) ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp]
    exact (AlgEquiv.injective _).comp <|
      Module.FaithfullyFlat.tensorProduct_mk_injective (A ⧸ I)
  intro x hx
  rw [Ideal.mem_comap] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply inj
  have : (AlgEquiv.toLinearMap (Algebra.TensorProduct.tensorQuotEquivQuotIdealMap B I) ∘ₗ
      TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
    simp [← Algebra.algebraMap_eq_smul_one, hx]
  simp [this]

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
lemma Ideal.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I ↦ ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := fun I ↦
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B) I).mpr
      I.asIdeal.comap_map_eq_self_of_faithfullyFlat

/-- If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `A`-algebra. -/
lemma Module.FaithfullyFlat.of_primeSpectrum_comap_surjective [Flat A B]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m', hm']
  rw [Ideal.smul_top_eq_map, this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    fun top ↦ m'.isPrime.ne_top <| top_le_iff.mp <| top ▸ Ideal.map_comap_le

/-- If `B` is a local, flat `A`-algebra and `A →+* B` is local, `B` is faithfully flat. -/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≤
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 2).mp ‹_›
  rw [eqt, top_le_iff, Submodule.restrictScalars_eq_top_iff] at this
  exact Ideal.IsPrime.ne_top' this
