import Mathlib

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The height of a prime ideal in a ring is the supremum over the lengths of prime ideal
chains ending at `p`. -/
noncomputable def Ideal.primeHeight (p : Ideal A) : WithTop ℕ :=
  Set.chainHeight { q : Ideal A | q.IsPrime ∧ q < p }

-- TODO: remove this in favour of `IsLocalization.primeHeight_eq_ringKrullDim`
/-- The height of a prime ideal `p` equals to the dimension of `A` localized away from `p`. -/
lemma Ideal.primeHeight_eq_ringKrullDim (p : Ideal A) [p.IsPrime] :
    p.primeHeight = ringKrullDim (Localization.AtPrime p) :=
  sorry

/-- If `B = Aₚ`, `dim B = ht(p)`. -/
lemma IsLocalization.primeHeight_eq_ringKrullDim (p : Ideal A) [p.IsPrime]
    [Algebra A B] [IsLocalization.AtPrime B p] :
    p.primeHeight = ringKrullDim B :=
  sorry

-- TODO
/-- `dim A ≤ n` if and only if the height of all prime ideals is less than `n`. -/
lemma ringKrullDim_le_of_height_le [Nontrivial A] (n : WithBot (WithTop ℕ)) :
  ringKrullDim A ≤ n ↔
    ∀ (p : Ideal A), p.IsPrime → p.primeHeight ≤ n :=
  sorry

lemma Ideal.exists_isMaximal_height_eq_of_nontrivial [Nontrivial A] :
    ∃ (p : Ideal A), p.IsMaximal ∧ p.primeHeight = ringKrullDim A :=
  sorry

lemma height_eq_of_ringEquiv (e : A ≃+* B) (p : Ideal A) [p.IsPrime] :
    (p.map e).primeHeight = p.primeHeight :=
  sorry

lemma IsLocalization.height_eq_of_disjoint [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (p : Ideal A) [p.IsPrime] (h : Disjoint (M : Set A) (p : Set A)) :
    (p.map <| algebraMap A B).primeHeight = p.primeHeight :=
  sorry
