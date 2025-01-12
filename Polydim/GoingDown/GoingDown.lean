import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The going-down theorem for flat algebras. -/
lemma exists_isPrime_and_liesOver_of_isPrime_of_le_of_liesOver [Module.Flat A B] (p' p : Ideal A)
    [p'.IsPrime] [p.IsPrime]
    (hle : p' ≤ p) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    ∃ (P' : Ideal B), P'.IsPrime ∧ P'.LiesOver p := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by
    -- this is in Mathlib
    sorry
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p P (algebraMap A B) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime P) :=
    -- local + flat = faithfully flat
    sorry
  let pl' : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A _) p'
  have : ∃ (Pl' : Ideal (Localization.AtPrime P)), Pl'.IsPrime ∧ Pl'.LiesOver pl' :=
    -- use faithful flatness
    sorry
  obtain ⟨Pl', hl, hlo⟩ := this
  refine ⟨Ideal.comap (algebraMap B _) Pl', ?_, ?_⟩
  · sorry
  · sorry
