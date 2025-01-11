import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.Flat A B]

lemma Module.tensorProduct_mk_injective_of_isScalarTower (M : Type*) [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] :
    Function.Injective (TensorProduct.mk A B M) :=
  -- consider `B ⊗[A] M →ₗ[B] M, b ⊗ m ↦ b • m`
  sorry

/-- If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective. -/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective [Module.FaithfullyFlat A B]
      (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M) :=
  -- denote the map by `τ`
  -- use `Module.tensorProduct_mk_injective_of_isScalarTower` for `M = B ⊗[A] M`
  -- to show `B ⊗ ker (τ) = 0`, then conclude by
  -- `Module.FaithfullyFlat.lTensor_reflects_triviality`.
  sorry

-- Bonus
/-- If `M →ₗ[A] B ⊗[A] M` is injective for every `A`-module `M`, `B` is a faithfully flat
`A`-algebra. -/
lemma Module.FaithfullyFlat.of_tensorProduct_mk_injective
    (h : ∀ (M : Type*) [AddCommGroup M] [Module A M], Function.Injective (TensorProduct.mk A B M)) :
    FaithfullyFlat A B :=
  -- easy, use `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`
  sorry

/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat [Module.FaithfullyFlat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  apply le_antisymm
  · -- use `Module.FaithfullyFlat.tensorProduct_mk_injective` for `M = A ⧸ I`
    -- and consider the map `A / I →+* (A / I) ⊗[A] B ≃+* B ⧸ (I.map <| algebraMap A B)`
    sorry
  · exact le_comap_map

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
lemma Ideal.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  -- easy from `Ideal.comap_map_eq_self_of_faithfullyFlat`
  sorry

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
  -- easy from `Ideal.comap_surjective_of_faithfullyFlat`
  sorry

-- Bonus
/-- If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `A`-algebra. -/
lemma Module.FaithfullyFlat.of_primeSpectrum_comap_surjective
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Module.FaithfullyFlat A B :=
  sorry

/-- If `B` is a local, flat `A`-algebra and `A →+* B` is local, `B` is faithfully flat. -/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  -- use `Module.faithfullyFlat_iff` and `Ideal.smul_top_eq_map`
  sorry
