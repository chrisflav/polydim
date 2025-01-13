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


section

#check PrimeSpectrum.equivSubtype
#check IsLocalization.AtPrime.orderIsoOfPrime
#check Order.krullDim_eq_of_orderIso
#check Subtype.strictMono_coe

def PrimeSpectrum.orderIso (R : Type*) [CommSemiring R] :
    PrimeSpectrum R ≃o { q : Ideal R // q.IsPrime } :=
  Equiv.toOrderIso (PrimeSpectrum.equivSubtype R)
  (fun _ _ hle ↦ hle) (fun _ _ hle ↦ hle)

def PrimeSpectrum.orderIsoOfProp (R : Type*) [CommSemiring R] (motive : Ideal R → Prop) :
    { q : PrimeSpectrum R // motive q.asIdeal } ≃o { q : Ideal R // q.IsPrime ∧ motive q} where
  toFun q := ⟨q.val.asIdeal, ⟨q.val.isPrime, q.prop⟩⟩
  invFun q := ⟨⟨q, q.prop.1⟩, q.prop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    rfl

def IsLocalization.AtPrime.orderIsoOfPrimeSpectrum {R : Type*} [CommSemiring R] (S : Type*)
    [CommSemiring S] [Algebra R S] (p : Ideal R) [hp : p.IsPrime] [IsLocalization.AtPrime S p] :
    PrimeSpectrum S ≃o { q : PrimeSpectrum R // q ≤ ⟨p, hp⟩ } :=
  OrderIso.trans
  (OrderIso.trans (PrimeSpectrum.orderIso S) (IsLocalization.AtPrime.orderIsoOfPrime S p))
  (PrimeSpectrum.orderIsoOfProp R (fun I ↦ (I ≤ p))).symm

end

section

#check Order.krullDim_le_of_strictMono
#check Order.height_le_height_apply_of_strictMono

variable {α : Type u_1} {s : Set α} [Preorder α] (a : α)

theorem chainHeight_eq_krullDim (hs : Nonempty s): s.chainHeight = Order.krullDim s := sorry
theorem chainHeight_le_eq_height : Set.chainHeight {b | b ≤ a} = Order.height a := sorry
theorem Order.hieght_eq_krullDim_le : Order.height a = Order.krullDim {b // b ≤ a} := sorry

end



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
