import Polydim.Dimension.Height

variable {R : Type*} [CommRing R]

section FromAndrewsRepo

section

variable {M : Type*} [AddCommMonoid M] [Module R M]

-- from Andrews repo:

noncomputable def Submodule.minGeneratorCard (p : Submodule R M) : ℕ :=
  ⨅ s : { s : Set M // s.Finite ∧ Submodule.span R s = p}, s.2.1.toFinset.card

noncomputable def Submodule.spanrank (p : Submodule R M) : WithTop ℕ :=
  ⨅ s : { s : Set M // s.Finite ∧ Submodule.span R s = p}, s.2.1.toFinset.card

lemma Submodule.exists_finset_span_eq_of_fg (p : Submodule R M) (h : p.FG) :
    ∃ (s : Finset M), Submodule.span R s = p ∧ s.card = p.spanrank :=
  sorry

end

-- `ideal.height_le_iff_exists_minimal_primes` from Andrews repository.
theorem Ideal.height_le_iff_exists [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (n : WithTop ℕ) :
    p.primeHeight ≤ n ↔ ∃ (I : Ideal R), p ∈ I.minimalPrimes ∧ I.spanrank ≤ n :=
  sorry

-- `ideal.height_le_spanrank_of_mem_minimal_primes` from Andrews repository.
theorem Ideal.primeHeight_le_of_mem_minimalPrimes [IsNoetherianRing R] (p : Ideal R)
    [p.IsPrime] (I : Ideal R) (hI : p ∈ I.minimalPrimes) :
    p.primeHeight ≤ I.spanrank := by
  sorry

end FromAndrewsRepo
