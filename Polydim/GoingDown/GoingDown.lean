import Mathlib

import Polydim.GoingDown.FaithfullyFlat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

noncomputable instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] :
  Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

noncomputable instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] :
  IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    have : (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over) = algebraMap (Localization.AtPrime p) (Localization.AtPrime P) := rfl
    rw [← this]
    simp only [RingHom.coe_comp, Function.comp_apply, Localization.localRingHom_to_map]
    exact rfl

instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
  Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by sorry

/-- The going-down theorem for flat algebras. -/
lemma exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver [Module.Flat A B] (p' p : Ideal A)
    [p'.IsPrime] [p.IsPrime]
    (hle : p' ≤ p) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    ∃ (P' : Ideal B), P'.IsPrime ∧ P'.LiesOver p' := by
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p P (algebraMap A B) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime P) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have disj : Disjoint (p.primeCompl : Set A) p' := by simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hle]
  let pl' : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A _) p'
  have : ∃ (Pl' : Ideal (Localization.AtPrime P)), Pl'.IsPrime ∧ Pl'.LiesOver pl' := by
    have hp : pl'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ p' (by simpa) disj
    obtain ⟨Pl, hpl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := Localization.AtPrime P) ⟨pl', hp⟩
    exact ⟨Pl.asIdeal, ⟨PrimeSpectrum.isPrime Pl, ⟨by rw [Ideal.under_def, ← PrimeSpectrum.comap_asIdeal, hpl]⟩⟩⟩
  obtain ⟨Pl', hl, hlo⟩ := this
  refine ⟨Ideal.comap (algebraMap B _) Pl', ?_, ?_⟩
  · exact Ideal.IsPrime.under B Pl'
  · unfold pl' at hlo
    replace hlo := hlo.over
    constructor
    rw [← Ideal.under_def, Ideal.under_under,
      ← Ideal.under_under (B := (Localization.AtPrime p)) Pl', ← hlo, Ideal.under_def,
      IsLocalization.comap_map_of_isPrime_disjoint _ _ p' (by simpa) disj]
