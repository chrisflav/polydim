import Polydim.Dimension.KrullHeightFromAndrew

variable {R : Type*} [CommRing R]

/-- If `p` is a prime in a Noetherian ring `R`, there exists a `p`-primary ideal `I`
spanned by `p.primeHeight` elements. -/
lemma Ideal.exists_card_eq_primeHeight_of_isNoetherianRing [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] :
    ∃ (I : Ideal R) (s : Finset R), p ∈ I.minimalPrimes ∧ Ideal.span s = I ∧ s.card = p.primeHeight := by
  obtain ⟨I, hI, hr⟩ := (p.height_le_iff_exists p.primeHeight).mp le_rfl
  obtain ⟨s, hs, hc⟩ := I.exists_finset_span_eq_of_fg (IsNoetherian.noetherian I)
  refine ⟨I, s, hI, hs, ?_⟩
  rw [hc]
  exact le_antisymm hr <| p.primeHeight_le_of_mem_minimalPrimes I hI

lemma Ideal.primeHeight_le_of_mem_minimalPrimes' [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (I : Ideal R) (hI : p ∈ I.minimalPrimes)
    (s : Finset R) (hs : Ideal.span s = I) :
    p.primeHeight ≤ s.card := by
  have : I.spanrank ≤ s.card := by
    simp only [Submodule.spanrank]
    let hsf' : { s : Set R // s.Finite ∧ Submodule.span R s = I} :=
      ⟨s, s.finite_toSet, hs⟩
    have : ↑s.card = hsf'.2.1.toFinset.card := by simp
    rw [this]
    apply ciInf_le'
  apply le_trans ?_ this
  apply p.primeHeight_le_of_mem_minimalPrimes
  exact hI

variable {S : Type*} [CommRing S] [Algebra R S]

@[simp]
lemma Ideal.comap_map_quotient_mk {R : Type*} [CommRing R] (I J : Ideal R) :
    (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J := by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup]
  rw [sup_comm]

lemma Ideal.map_quotient_mk_isPrime_of_isPrime {R : Type*} [CommRing R]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (hIP : I ≤ p) :
    (p.map (Ideal.Quotient.mk I)).IsPrime := by
  apply Ideal.map_isPrime_of_surjective
  exact Quotient.mk_surjective
  simpa

lemma primeHeight_le_primeHeight_add_of_liesOver [IsNoetherianRing R]
      [IsNoetherianRing S] (p : Ideal R) [p.IsPrime]
      (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    P.primeHeight ≤ p.primeHeight +
      (P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))).primeHeight := by
  classical
  obtain ⟨Ip, sp, hIp, hsp, hcp⟩ := Ideal.exists_card_eq_primeHeight_of_isNoetherianRing p
  set P' := P.map (Ideal.Quotient.mk <| p.map (algebraMap R S))
  have : P'.IsPrime := by
    apply Ideal.map_quotient_mk_isPrime_of_isPrime
    rw [Ideal.map_le_iff_le_comap]
    rw [Ideal.LiesOver.over (p := p) (P := P)]
  obtain ⟨IP', sP', hIP', hsP', hcP'⟩ := Ideal.exists_card_eq_primeHeight_of_isNoetherianRing P'
  -- horror starts
  have : ∀ x ∈ P', ∃ y ∈ P, Ideal.Quotient.mk _ y = x := by
    simp [P']
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_quotient_iff_mem] at hx
    use y
    rw [Ideal.map_le_iff_le_comap]
    rw [Ideal.LiesOver.over (p := p) (P := P)]
  choose g hg using this
  have hsP'sub : (sP' : Set <| S ⧸ (Ideal.map (algebraMap R S) p)) ⊆ (P' : Set <| S ⧸ _) := by
    intro x hx
    apply hIP'.1.2
    rw [← hsP']
    apply Ideal.subset_span
    exact hx
  let o : Finset S :=
    Finset.image (fun x : sP' ↦ g x.val <| hsP'sub x.2) Finset.univ
  have ho : (o : Set S) ⊆ (P : Set S) := by
    simp [o]
    intro x hx
    simp
    apply (hg _ _).1
  have hcardo : Finset.card o ≤ Finset.card sP' := by
    simp [o]
    apply le_trans
    · apply Finset.card_image_le
    · simp
  have himgo : Finset.image (Ideal.Quotient.mk _) o = sP' := by
    ext x
    constructor
    · intro hx
      simp [o] at hx
      obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hx
      rwa [(hg _ _).2]
    · intro hx
      simp [o]
      use g x (hsP'sub hx)
      constructor
      use x, hx
      apply (hg _ _).2
  -- horror ends
  rw [← hcP', ← hcp]
  let t : Finset S := Finset.image (algebraMap R S) sp ∪ o
  have ht : t.card ≤ sp.card + sP'.card := by
    simp only [t]
    apply le_trans
    · apply Finset.card_union_le
    · apply add_le_add
      exact Finset.card_image_le
      exact hcardo
  have : P.primeHeight ≤ t.card := by
    fapply Ideal.primeHeight_le_of_mem_minimalPrimes'
    · exact Ideal.span t
    · refine ⟨⟨inferInstance, ?_⟩, ?_⟩
      · rw [Ideal.span_le]
        simp only [t, Finset.coe_union]
        rw [Set.union_subset_iff]
        simp
        constructor
        · intro x hx
          rw [← Ideal.coe_comap, ← Ideal.under_def, ← Ideal.LiesOver.over (P := P) (p := p)]
          have : Ip ≤ p := hIp.1.2
          simp only [SetLike.mem_coe]
          apply this
          rw [← hsp]
          apply Ideal.subset_span
          exact hx
        · intro x hx
          apply ho
          exact hx
      · intro q ⟨_, hleq⟩ hqle
        have h1 : Ideal.map (algebraMap R S) Ip ≤ q := by
          rw [← hsp]
          rw [Ideal.map_span]
          apply le_trans ?_ hleq
          · rw [Ideal.span_le]
            rintro x ⟨y, hy, rfl⟩
            apply Ideal.subset_span
            simp [t]
            apply Or.inl
            use y, hy
        have h2 : Ideal.map (algebraMap R S) p ≤ q := by
          rw [Ideal.map_le_iff_le_comap]
          apply hIp.2
          constructor
          · infer_instance
          · rw [← Ideal.map_le_iff_le_comap]
            exact h1
          · rw [Ideal.LiesOver.over (P := P) (p := p), Ideal.under_def]
            apply Ideal.comap_mono
            exact hqle
        have : P' ≤ q.map (Ideal.Quotient.mk (p.map (algebraMap R S))) := by
          apply hIP'.2
          constructor
          · apply Ideal.map_quotient_mk_isPrime_of_isPrime
            exact h2
          · apply le_trans ?_ (Ideal.map_mono hleq)
            apply le_trans ?_ (Ideal.map_mono <| Ideal.span_mono <| Finset.subset_union_right)
            show IP' ≤ Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p))
                (Ideal.span o)
            rw [← hsP']
            rw [Ideal.span_le]
            intro x hx
            simp only [Finset.coe_image, SetLike.mem_coe]
            rw [← himgo] at hx
            simp at hx
            obtain ⟨y, hy, rfl⟩ := hx
            apply Ideal.mem_map_of_mem
            apply Ideal.subset_span
            exact hy
          · apply Ideal.map_mono
            exact hqle
        have hP'le : P'.comap (Ideal.Quotient.mk _) ≤ Ideal.comap
            (Ideal.Quotient.mk (p.map (algebraMap R S)))
            (q.map (Ideal.Quotient.mk (p.map (algebraMap R S)))) := by
          apply Ideal.comap_mono
          exact this
        simpa [P', h2] using hP'le
    · rfl
  apply le_trans this
  rw [← Nat.cast_add]
  apply Nat.mono_cast
  exact ht
