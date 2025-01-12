import Mathlib

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
   (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

lemma IsLocalization.comap_map :
    (I.map (algebraMap R S)).comap (algebraMap R S) =
      ⨆ m ∈ M, Submodule.colon I (Ideal.span {m}) := by
  ext x
  constructor
  · intro hx
    simp at hx
    rw [IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨a, m⟩, hx⟩ := hx
    simp at hx
    rw [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 hx
    sorry
  · sorry

lemma IsLocalization.map_ne_top_of_disjoint (h : Disjoint (M : Set R) (I : Set R)) :
    I.map (algebraMap R S) ≠ ⊤ := by
  intro hc
  have : 1 ∈ Ideal.map (algebraMap R S) I := by
    rw [hc]
    trivial
  rw [IsLocalization.mem_map_algebraMap_iff M] at this
  obtain ⟨⟨a, m⟩, hx⟩ := this
  simp at hx
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 hx
  rw [Set.disjoint_left] at h
  have : c.val * m.val ∈ M := M.mul_mem c.2 m.2
  apply h this
  rw [hc]
  apply Ideal.mul_mem_left
  exact a.2

end

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma PrimeSpectrum.mem_range_comap_iff (p : PrimeSpectrum R) :
    p ∈ Set.range (PrimeSpectrum.comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q, rfl⟩
    simp
  · let M : Submonoid S := Submonoid.map f p.asIdeal.primeCompl
    have : (p.asIdeal.map f).map (algebraMap S (Localization M)) ≠ ⊤ := by
      apply IsLocalization.map_ne_top_of_disjoint M
      rw [Set.disjoint_left]
      rintro a ⟨x, (hx : x ∉ p.asIdeal), rfl⟩
      rwa [← hp] at hx
    obtain ⟨m, _, hle⟩ := Ideal.exists_le_maximal _ this
    let q : Ideal S := m.comap (algebraMap S (Localization M))
    have h1 : p.asIdeal ≤ q.comap f := by
      rw [← hp, ← Ideal.map_le_iff_le_comap, Ideal.map_comap_map]
      simpa only [q, ← Ideal.map_le_iff_le_comap]
    have hd : Disjoint (M : Set S) (q : Set S) :=
      ((IsLocalization.isPrime_iff_isPrime_disjoint M _ m).mp inferInstance).right
    have h2 : q.comap f ≤ p.asIdeal := by
      simp only [Submonoid.coe_map, M, Set.disjoint_right] at hd
      intro x (hx : x ∈ f ⁻¹' q)
      have : x ∉ p.asIdeal.primeCompl := by
        intro ha
        apply hd hx
        simp only [Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
        use x
      simpa [Ideal.primeCompl] using this
    exact ⟨⟨q, inferInstance⟩, le_antisymm h2 h1⟩
