import Verification.defs_timeHT

open HofT

universe T

/-
Axioms to ensure the successor and predecessor relation is a total, linear order
-/
axiom transitivity {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A B C : timeline κ n),
  (B ∈ succs A τ ∧ C ∈ succs B τ)
  → C ∈ succs A τ

axiom irreflexivity {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A : timeline κ n),
  ¬(A ∈ succs A τ)

axiom totality {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (A ∈ ffld τ ∧ B ∈ ffld τ ∧ valid_timeline τ)
  → (A ∈ succs B τ ∨ A = B ∨ B ∈ succs A τ)

theorem FUNDAMENTAL {κ : Type T} :
  ∀ (n : ℕ)
  (τ : Set (timeline κ n × timeline κ n)),
  ∃ (t : timeline κ (n + 1)),
  t = τ := by
  intro n T
  exact ⟨T, rfl⟩




/-
!SING# : Theorems regarding single timelines
SING0 : The cardinality of a timeline that is single is exact 1
SING1 : Any proper subset ("proper subset" meaning, for example, A ⊆ B ∧ A ≠ B)
        of a single timeline is equal to the empty set
-/
theorem SING0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  single τ → Set.ncard τ = 1 := by
    intro T singT
    unfold single at singT
    rcases singT with ⟨nempt, p, hp⟩
    have sthm1 : T = {p} := by
      rw [Set.ext_iff]
      intro x
      have ssthm1 := hp x
      simp only [Set.mem_singleton_iff]
      exact ssthm1
    simp only [Set.ncard_eq_one]
    exact ⟨p, sthm1⟩

theorem SING1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  single τ → ∀ X ⊆ τ, Set.ncard X < Set.ncard τ
  → X = ∅ := by
  intro T singT X subX lessX
  unfold single at singT
  have sthm1 := SING0 T singT
  rw [sthm1] at lessX
  have zeroX : X.ncard = 0 := by
    exact Nat.lt_one_iff.mp lessX
  rw [Set.empty_def]
  rw [Set.ext_iff]
  intro x
  rw [Set.subset_def] at subX
  have sthm2 : T.ncard ≠ 0 := by
    omega
  have sthm3 : T.Finite := by
    exact Set.finite_of_ncard_ne_zero sthm2
  have sthm4 : X.Finite := sthm3.subset subX
  constructor
  · intro h1
    simp only [Set.setOf_false, Set.mem_empty_iff_false]
    have exi : X.Nonempty := ⟨x, h1⟩
    have sthm5 : Set.ncard X > 0 := by
      exact exi.ncard_pos sthm4
    omega
  · intro h2
    simp only [Set.setOf_false, Set.mem_empty_iff_false] at h2





/-
!INV# : Theorems regarding inverse timelines
INV0 - Each pair inside of T has its inverse as an
        element of the inverse timeline of T (and vice versa).
INV1 - The inverse pair of the inverse pair of any
        given element of a timeline is equal to the element itself.
F_INV0 - The inverse timeline of an inverse timeline of a timeline T is equal to T itself.
INV2 - If a timeline is valid, then it is nonbranching.
INV3 - If a timeline is nonbranching, then its inverse is nonbranching.
INV4 - If a timeline is ordered then its inverse is ordered.
INV5 - If a timeline is valid, then its inverse is nonempty.
INV6 - If a timeline is valid, then its inverse is strictly ordered.
F_INV1 - If a timeline is valid, then its inverse is valid.
INV7 - If a timeline is valid, then its inverse has its same field.
INV8 - If an ordered pair is an element of a valid timeline T, then its inverse pair is not in T
-/
theorem INV0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ∀ p, p ∈ τ ↔ inv_pair p ∈ inv_timeline τ := by
  unfold inv_pair
  unfold inv_timeline
  intro T I
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hp1
    exact ⟨I, hp1, rfl, rfl⟩
  · intro hp2
    rcases hp2 with ⟨q, hq, c1, c2⟩
    have hIq : I = q := Prod.ext c2 c1
    rw [hIq]
    exact hq

theorem INV1 {κ : Type T} {n : ℕ} :
  ∀ (p : timeline κ n × timeline κ n),
  (inv_pair (inv_pair p) = p) := by
  unfold inv_pair
  intro p
  rw []

theorem INV {κ : Type T} {n : ℕ} :
  ∀ (p q : timeline κ n × timeline κ n),
  inv_pair p = inv_pair q ↔ p = q := by
  intro p q
  constructor
  · intro hp1
    have sthm1 : inv_pair (inv_pair p) = inv_pair (inv_pair q) := by
      rw [hp1]
    have sthm2 := INV1 p
    have sthm3 := INV1 q
    rw [sthm2] at sthm1
    rw [sthm3] at sthm1
    exact sthm1
  · intro hp2
    rw [hp2]

theorem F_INV0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  inv_timeline (inv_timeline τ) = τ := by
  intro T
  have thm1 : ∀ p ∈ T, inv_pair (inv_pair p) = p := by
    intro p hp
    exact INV1 p
  have thm2 : ∀ p, p ∈ T ↔ inv_pair (inv_pair p) ∈ inv_timeline (inv_timeline T) := by
    intro p
    have sthm1 := INV0 T p
    have sthm2 := INV0 (inv_timeline T) (inv_pair p)
    constructor
    · intro hp1
      have ssthm1 := sthm1.mp hp1
      have ssthm2 := sthm2.mp ssthm1
      exact ssthm2
    · intro hp2
      have ssthm1 := sthm2.mpr hp2
      have ssthm2 := sthm1.mpr ssthm1
      exact ssthm2
  have thm3 : ∀ p, p ∈ T ↔ p ∈ inv_timeline (inv_timeline T) := by
    exact thm2
  have finalthm : T = inv_timeline (inv_timeline T) := by
    ext p
    exact thm3 p
  exact finalthm.symm

theorem INV2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → nonbranching τ := by
  unfold valid_timeline
  intro T hp
  rcases hp with ⟨ha, hb, hc, hd⟩
  exact ha

theorem INV3 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  nonbranching τ → nonbranching (inv_timeline τ) := by
  unfold nonbranching
  intro T Tn p pi q qi
  let inv_q := inv_pair q
  let inv_p := inv_pair p
  have hq := INV0 T inv_q
  have hp := INV0 T inv_p
  have subp := INV1 inv_q
  have subq := INV1 inv_p
  have sub1 : inv_q ∈ T ↔ q ∈ inv_timeline T := by
    exact hq
  have sub2 : inv_p ∈ T ↔ p ∈ inv_timeline T := by
    exact hp
  have sub3 : inv_pair q ∈ T ↔ q ∈ inv_timeline T := by
    change inv_q ∈ T ↔ q ∈ inv_timeline T
    exact sub1
  have sub4 : inv_pair p ∈ T ↔ p ∈ inv_timeline T := by
    change inv_p ∈ T ↔ p ∈ inv_timeline T
    exact sub2
  have hh1 : inv_pair p ∈ T := by
    exact sub4.mpr pi
  have hh2 : inv_pair q ∈ T := by
    exact sub3.mpr qi
  have f : (inv_pair q).1 = (inv_pair p).1 ↔ (inv_pair q).2 = (inv_pair p).2 := by
    exact Tn (inv_pair q) hh2 (inv_pair p) hh1
  have eq1 : (inv_pair q).1 = q.2 := by
    rfl
  have eq2 : (inv_pair q).2 = q.1 := by
    rfl
  have eq3 : (inv_pair p).1 = p.2 := by
    rfl
  have eq4 : (inv_pair p).2 = p.1 := by
    rfl
  simpa [eq1, eq2, eq3, eq4, eq_comm] using f.symm

theorem INV4 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ordered τ → ordered (inv_timeline τ) := by
  unfold ordered
  unfold single
  intro T
  intro P1
  rcases P1 with h1 | h2
  --First case of the proof (singletons)
  rcases h1 with ⟨h11, h12⟩
  have nonempty : ∃ p, p ∈ T := by
    exact h11
  rcases nonempty with ⟨pair, Hx⟩
  have sthm0 := INV0 T pair
  have sthm1 : (inv_timeline T).Nonempty := by
    have ssthm0 : (inv_pair pair) ∈ inv_timeline T := by
      exact sthm0.mp Hx
    exact ⟨inv_pair pair, ssthm0⟩
  have sthm2 : ∃ q, ∀ p, inv_pair p ∈ inv_timeline T ↔ p = q := by
    rcases h12 with ⟨X, Y⟩
    have ssthm4 : ∀ p, inv_pair p ∈ inv_timeline T ↔ p = X := by
      intro p
      have sssthm1 := INV0 T p
      have sssthm2 : p ∈ T ↔ p = X := by
        exact Y p
      constructor
      · intro hp1
        have shp1 := sssthm1.mpr hp1
        have shp2 := sssthm2.mp shp1
        exact shp2
      . intro hp2
        have shp1 := sssthm2.mpr hp2
        have shp2 := sssthm1.mp shp1
        exact shp2
    exact ⟨X, ssthm4⟩
  have sthm3 : ∃ q, ∀ p, p ∈ inv_timeline T ↔ p = q := by
    rcases sthm2 with ⟨Z, Y⟩
    let X := inv_pair Z
    have ssthm0 : ∀ p, inv_pair p = Z ↔ p = X := by
      intro p
      have sssthm1 := INV1 Z
      have sssthm2 := INV1 p
      dsimp [X]
      constructor
      · intro shp1
        rw [← sssthm2, shp1]
      · intro shp2
        rw[shp2, sssthm1]
    have ssthm1 : ∀ p, p ∈ inv_timeline T ↔ p = X := by
      intro p
      let r := inv_pair p
      have sssthm1 : inv_pair r ∈ inv_timeline T ↔ r = Z := by
        exact Y r
      have sssthm2 : inv_pair r = p := by
        rfl
      dsimp [r] at sssthm1
      have sssthm3 : p ∈ inv_timeline T ↔ inv_pair p = Z := by
        exact sssthm1
      have sssthm4 : p ∈ inv_timeline T ↔ p = X := by
        have ssssthm1 : inv_pair p = Z ↔ p = X := by
          exact ssthm0 p
        constructor
        · intro shp1
          have sshp1 := sssthm3.mp shp1
          have sshp2 := ssssthm1.mp sshp1
          exact sshp2
        · intro shp2
          have sshp1 := ssssthm1.mpr shp2
          have sshp2 := sssthm3.mpr sshp1
          exact sshp2
      exact sssthm4
    exact ⟨X, ssthm1⟩
  have thm1 : ordered (inv_timeline T) := by
    left
    unfold single
    constructor
    · exact sthm1
    · exact sthm3
  exact thm1
  --Second case: Non-singeltons
  right
  intro hp1
  have sthm1 : ∃ ℓ, ℓ ∈ inv_timeline T := by
    exact hp1
  have sthm2 : ∃ ℓ, ℓ ∈ T := by
    rcases sthm1 with ⟨ρ, hpp⟩
    have ssthm1 : inv_pair ρ ∈ T := by
      have sssthm1 := INV0 T (inv_pair ρ)
      have sssthm2 := INV1 ρ
      rw [sssthm2.symm] at hpp
      exact sssthm1.mpr hpp
    exact ⟨inv_pair ρ, ssthm1⟩
  have sthm3 : ∀ p ∈ T, ∃ q ∈ T, p ≠ q ∧ (p.1 = q.2 ∨ p.2 = q.1) := by
    exact h2 sthm2
  have sthm4 : ∀ p ∈ T, ∃ q ∈ T, inv_pair p ≠ inv_pair q ∧ (p.1 = q.2 ∨ p.2 = q.1) := by
    intro p
    rcases sthm2 with ⟨q, hq⟩
    intro hp2
    have ssthm3 := sthm3 p hp2
    rcases ssthm3 with ⟨r, hr⟩
    rcases hr with ⟨h1, h2, h3⟩
    have ssthm1 := (INV p r).mp
    have ssthm2 : p ≠ r → inv_pair p ≠ inv_pair r := mt ssthm1
    have ssthm4 : inv_pair p ≠ inv_pair r := by
      exact ssthm2 h2
    exact ⟨r, h1, ssthm4, h3⟩
  have sthm5 : ∀ (p q : timeline κ n × timeline κ n),
    (p.1 = q.2 ∨ p.2 = q.1) ↔ ((inv_pair p).1 = (inv_pair q).2 ∨ (inv_pair p).2 = (inv_pair q).1) := by
    intro p q
    have ssthm1 : p.1 = q.2 ↔ (inv_pair p).2 = (inv_pair q).1 := by
      unfold inv_pair
      rfl
    have ssthm2 : p.2 = q.1 ↔ (inv_pair p).1 = (inv_pair q).2 := by
      unfold inv_pair
      rfl
    constructor
    · intro shp1
      rcases shp1 with oshp11 | oshp12
      right
      rw [ssthm1] at oshp11
      exact oshp11
      left
      rw [ssthm2] at oshp12
      exact oshp12
    · intro shp2
      rcases shp2 with oshp11 | oshp12
      right
      rw [ssthm2.symm] at oshp11
      exact oshp11
      left
      rw [ssthm1.symm] at oshp12
      exact oshp12
  have sthm6 : ∀ p ∈ T, ∃ q ∈ T,
    (inv_pair p ≠ inv_pair q ∧ ((inv_pair p).1 = (inv_pair q).2 ∨ (inv_pair p).2 = (inv_pair q).1)) := by
    intro p
    intro shp1
    have ssthm1 := sthm4 p shp1
    rcases ssthm1 with ⟨r, hr⟩
    rcases hr with ⟨h1, h2, h3⟩
    have ssthm2 := sthm5 p r
    rw [ssthm2] at h3
    exact ⟨r, h1, h2, h3⟩
  intro p
  intro hp
  have sthm7 : p ∈ inv_timeline T ↔ inv_pair p ∈ T := by
    have ssthm1 := (INV0 T (inv_pair p)).symm
    have ssthm2 := INV1 p
    rw [ssthm2] at ssthm1
    exact ssthm1
  rw [sthm7] at hp
  have sthm8 := sthm6 (inv_pair p) hp
  rcases sthm8 with ⟨r, hr⟩
  rcases hr with ⟨h1, h2, h3⟩
  have sthm9 := INV0 T r
  rw [sthm9] at h1
  have sthm10 := INV1 p
  rw [sthm10] at h2
  rw [sthm10] at h3
  exact ⟨(inv_pair r), h1, h2, h3⟩

theorem INV5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (inv_timeline τ).Nonempty := by
  unfold valid_timeline
  intro T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  have sthm1 : ∃ ℓ, ℓ ∈ T := by
    exact h4
  rcases sthm1 with ⟨r, hr⟩
  have sthm2 := (INV0 T r).mp hr
  exact ⟨inv_pair r, sthm2⟩

theorem INV6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → strictly_ordered (inv_timeline τ) := by
  unfold valid_timeline
  unfold strictly_ordered
  intro T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  intro B A p hp q hq
  have sthm1 := h3 A B (inv_pair p)
  have sthm2 := INV0 T (inv_pair p)
  have sthm3 := INV1 p
  rw [sthm3] at sthm2
  rw [sthm2] at sthm1
  have sthm4 := sthm1 hp (inv_pair q)
  have sthm5 := INV0 T (inv_pair q)
  have sthm6 := INV1 q
  rw [sthm6] at sthm5
  rw [sthm5] at sthm4
  have sthm7 := sthm4 hq
  have sthm8 : p.2 = A ∧ p.1 = B → q.1 ≠ A ∨ q.2 ≠ B := by
    have ssthm1 : ∀ (t : timeline κ n × timeline κ n),
      (inv_pair t).1 = t.2 := by
      unfold inv_pair
      intro p
      rfl
    have ssthm2 : ∀ (t : timeline κ n × timeline κ n),
      (inv_pair t).2 = t.1 := by
      unfold inv_pair
      intro p
      rfl
    rw [ssthm1 p] at sthm7
    rw [ssthm2 p] at sthm7
    rw [ssthm1 q] at sthm7
    rw [ssthm2 q] at sthm7
    exact sthm7
  intro fhp
  have sthm9 : p.1 = B ∧ p.2 = A → p.2 = A ∧ p.1 = B := by
    tauto
  have sthm10 := sthm9 fhp
  have sthm11 := sthm8 sthm10
  have sthm12 : q.1 ≠ A ∨ q.2 ≠ B ↔ q.2 ≠ B ∨ q.1 ≠ A := by
    exact or_comm
  rw [sthm12] at sthm11
  exact sthm11

theorem F_INV1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → valid_timeline (inv_timeline τ) := by
  unfold valid_timeline
  intro T hp
  have sthm1 := INV5 T hp
  have sthm2 := INV6 T hp
  rcases hp with ⟨h1, h2, h3, h4⟩
  have sthm3 := INV4 T h2
  have sthm4 := INV3 T h1
  exact ⟨sthm4, sthm3, sthm2, sthm1⟩

theorem INV7 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ → (ffld τ = ffld (inv_timeline τ)) := by
  intro T hT
  have sthm1 : ∀ p, p ∈ T → p.1 ∈ ffld T ∧ p.2 ∈ ffld T := by
    unfold ffld
    intro p hp
    rw [Set.mem_setOf_eq]
    rw [Set.mem_setOf_eq]
    have ssthm1 : T ∈ order_set n := by
      unfold order_set
      rw [Set.mem_setOf_eq]
      exact hT
    constructor
    · have sssthm1 : p.1 = p.1 ∨ p.2 = p.1 := by
        left
        rfl
      have sssthm2 : ∃ q ∈ T, q.1 = p.1 ∨ q.2 = p.1 := by
        exact ⟨p, hp, sssthm1⟩
      constructor
      · exact ssthm1
      · exact sssthm2
    · have sssthm1 : p.1 = p.2 ∨ p.2 = p.2 := by
        right
        rfl
      have sssthm2 : ∃ q ∈ T, q.1 = p.2 ∨ q.2 = p.2 := by
        exact ⟨p, hp, sssthm1⟩
      constructor
      · exact ssthm1
      · exact sssthm2
  unfold ffld
  have sthm2 : T ∈ order_set n ↔ (inv_timeline T) ∈ order_set n := by
    have ssthm1 := F_INV1 T
    have ssthm2 := F_INV1 (inv_timeline T)
    have ssthm3 := F_INV0 T
    rw [ssthm3] at ssthm2
    unfold order_set
    rw [Set.mem_setOf_eq]
    rw [Set.mem_setOf_eq]
    constructor
    · intro hp1
      exact ssthm1 hp1
    · intro hp2
      exact ssthm2 hp2
  have sthm3 : ∀ (p : timeline κ n × timeline κ n) (s : timeline κ n),
    (p.1 = s ∨ p.2 = s) ↔ ((inv_pair p).1 = s ∨ (inv_pair p).2 = s) := by
    intro p s
    have ssthm1 : (p.2, p.1).2 = p.1 := by
        rfl
    have ssthm2 : (p.2, p.1).1 = p.2 := by
        rfl
    constructor
    · intro hp1
      rcases hp1 with hp11 | hp12
      right
      unfold inv_pair
      rw [ssthm1]
      exact hp11
      left
      unfold inv_pair
      rw [ssthm2]
      exact hp12
    · intro hp2
      rcases hp2  with hp21 | hp22
      unfold inv_pair at hp21
      rw [ssthm2.symm]
      right
      exact hp21
      unfold inv_pair at hp22
      rw [ssthm1.symm]
      left
      exact hp22
  rw [sthm2]
  ext s
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hp1
    rcases hp1 with ⟨h1, h2⟩
    rcases h2 with ⟨X, hX⟩
    rcases hX with ⟨hX1, hX2⟩
    have ssthm1 := (INV0 T X).mp hX1
    have ssthm2 : ∃ p ∈ inv_timeline T, p.1 = s ∨ p.2 = s := by
      have sssthm1 := (sthm3 X s).mp hX2
      exact ⟨inv_pair X, ssthm1, sssthm1⟩
    constructor
    · exact h1
    · exact ssthm2
  · intro hp2
    rcases hp2 with ⟨h1, h2⟩
    rcases h2 with ⟨X, hX⟩
    rcases hX with ⟨hX1, hX2⟩
    have ssthm1 := (INV0 (inv_timeline T) X).mp hX1
    have eq := F_INV0 T
    rw [eq] at ssthm1
    have ssthm2 : ∃ p ∈ T, p.1 = s ∨ p.2 = s := by
      have sssthm1 := (sthm3 X s).mp hX2
      exact ⟨inv_pair X, ssthm1, sssthm1⟩
    constructor
    · exact h1
    · exact ssthm2

theorem INV8 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (p : timeline κ n × timeline κ n),
  (valid_timeline τ ∧ p ∈ τ) → inv_pair p ∉ τ := by
  intro T p hp
  rcases hp with ⟨hp1, hp2⟩
  have valid := hp1
  unfold valid_timeline at hp1
  rcases hp1 with ⟨h1, h2, h3, h4⟩
  unfold ordered at h2
  unfold nonbranching at h1
  have sthm1 := h1 p hp2 (inv_pair p)
  rcases h2 with h21 | h22
  unfold inv_pair
  unfold inv_pair at sthm1
  have sthm2 : (p.2, p.1) ∈ T → False := by
    intro hhp
    have ssthm1 := sthm1 hhp
    simp at ssthm1
    have ssthm1 : is_imm_succ p.2 p.1 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : p ∈ T ∧ p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · exact hp2
          · exact sssthm1
        exact ⟨p, sssthm2⟩
    have ssthm2 : is_imm_succ p.1 p.2 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : (p.2, p.1) ∈ T ∧ (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · exact hhp
          · exact sssthm1
        exact ⟨inv_pair p, sssthm2⟩
    have ssthm3 : p.2 ∈ succs p.1 T ∧ p.1 ∈ succs p.2 T := by
      unfold succs is_succ
      simp only [gt_iff_lt, ↓existsAndEq, and_true, Set.mem_setOf_eq]
      constructor
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm1
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm2
    have ssthm4 := transitivity n T p.1 p.2 p.1
    have ssthm5 : p.1 ∈ succs p.1 T := ssthm4 ssthm3
    have ssthm6 := irreflexivity n T p.1
    exact ssthm6 ssthm5
  contrapose sthm2
  push Not
  simp only [and_true]
  exact sthm2
  have sthm3 := h22 h4 p hp2
  have sthm4 : (p.2, p.1) ∈ T → False := by
    intro hhp
    have ssthm1 : is_imm_succ p.2 p.1 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : p ∈ T ∧ p.1 = p.1 ∧ p.2 = p.2 := by
          constructor
          · exact hp2
          · exact sssthm1
        exact ⟨p, sssthm2⟩
    have ssthm2 : is_imm_succ p.1 p.2 T := by
      unfold is_imm_succ
      constructor
      · exact valid
      · have sssthm1 : (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · rfl
          · rfl
        have sssthm2 : (p.2, p.1) ∈ T ∧ (p.2, p.1).1 = p.2 ∧ (p.2, p.1).2 = p.1 := by
          constructor
          · exact hhp
          · exact sssthm1
        exact ⟨inv_pair p, sssthm2⟩
    have ssthm3 : p.2 ∈ succs p.1 T ∧ p.1 ∈ succs p.2 T := by
      unfold succs is_succ
      simp only [gt_iff_lt, ↓existsAndEq, and_true, Set.mem_setOf_eq]
      constructor
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm1
      · refine ⟨1, ?_, ?_⟩
        · omega
        · exact ssthm2
    have ssthm4 := transitivity n T p.1 p.2 p.1
    have ssthm5 : p.1 ∈ succs p.1 T := ssthm4 ssthm3
    have ssthm6 := irreflexivity n T p.1
    exact ssthm6 ssthm5
  contrapose sthm4
  push Not
  simp only [and_true]
  exact sthm4





/-
!FLD# : Theorems regarding the field
FLD0 : The field of a valid timeline P, if P is a subset of another valid timeline T, is a subset
        of the field of T.
FLD1 :
-/
theorem FLD0 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ: Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ ρ ⊆ τ) → ffld ρ ⊆ ffld τ := by
  intro T P h
  rcases h with ⟨vT, vP, subPT⟩
  simp only [Set.subset_def]
  intro x hx
  simp only [Set.subset_def] at subPT
  unfold ffld
  simp only [Prod.exists, Set.mem_setOf_eq]
  constructor
  · unfold order_set
    simp only [Set.mem_setOf_eq]
    exact vT
  · unfold ffld at hx
    simp only [Prod.exists, Set.mem_setOf_eq] at hx
    rcases hx with ⟨hxv, hxe⟩
    unfold order_set at hxv
    simp only [Set.mem_setOf_eq] at hxv
    rcases hxe with ⟨y, z, hxef⟩
    rcases hxef with ⟨eps, eq⟩
    have sthm1 := subPT (y,z) eps
    exact ⟨y, z, sthm1, eq⟩





/-
!SP# : Theorems regarding successors and predecessors
SP0 : If a lower-order timeline B is an immediate successor of another lower-order timeline A
      within the field of some timeline T, then B is a succesor of A.
SP1 : If B is an immediate successor of A in T, then A is not an immediate successor of B in T.
SP2 :
SP3 :
SP4 :
SP5 :
SP6 :
-/
theorem SP0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  is_imm_succ B A τ → B ∈ succs A τ := by
    unfold succs is_succ
    intro T A B hB
    simp only [gt_iff_lt, Set.mem_setOf_eq]
    refine ⟨1, ?_, ?_⟩
    omega
    exact hB

theorem SP1 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  (is_imm_succ A B τ) → ¬is_imm_succ B A τ := by
  intro T A B h
  have sthm2 := transitivity n T B A B
  have sthm3 := irreflexivity n T B
  have sthm4 : ¬ ((is_imm_succ A B T) → ¬is_imm_succ B A T) → False := by
    push Not
    intro hp
    have ssthm1 := SP0 T B A hp.1
    have ssthm2 := SP0 T A B hp.2
    have ssthm3 : A ∈ succs B T ∧ B ∈ succs A T := by
      constructor
      · exact ssthm1
      · exact ssthm2
    have ssthm4 := sthm2 ssthm3
    exact sthm3 ssthm4
  push Not at sthm4
  contrapose sthm4
  push Not
  simp only [and_true]
  constructor
  · exact h
  · exact sthm4

theorem SP2 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  B ∈ succs A τ → A ∉ succs B τ := by
  intro T A B hB
  have transit := transitivity n T A B A
  have irreflex := irreflexivity n T A
  have contra : A ∈ succs B T → False := by
    intro hyp
    have fhyp : B ∈ succs A T ∧ A ∈ succs B T := ⟨hB, hyp⟩
    have ssthm1 := transit fhyp
    exact irreflex ssthm1
  contrapose contra
  push Not
  simp only [and_true]
  exact contra

theorem SP3 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  A ∈ succs B τ → A ∈ ffld τ ∧ B ∈ ffld τ := by
  intro T A B hA
  unfold succs is_succ at hA
  simp only [Set.mem_setOf_eq] at hA
  rcases hA with ⟨x, gr, hx⟩
  induction x generalizing A B with
  | zero => simp at gr
  | succ x ih =>
    cases x with
    | zero =>
      simp only [zero_add] at hx
      unfold is_imm_succ at hx
      unfold ffld
      unfold order_set
      simp only [Set.mem_setOf_eq]
      rcases hx with ⟨hx1, X, HX1, HX2, HX3⟩
      have or1 : X.1 = B ∨ X.2 = B := by
        left
        exact HX2
      have or2 : X.1 = A ∨ X.2 = A := by
        right
        exact HX3
      constructor
      · refine ⟨hx1, ?_⟩
        exact ⟨X, HX1, or2⟩
      · refine ⟨hx1, ?_⟩
        exact ⟨X, HX1, or1⟩
    | succ nt =>
      simp only [gt_iff_lt, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, true_and] at hx
      simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, Order.lt_two_iff, zero_le, or_true,
        Order.lt_add_one_iff, forall_const] at gr ih
      rcases hx with ⟨X, iS, iIS⟩
      unfold is_succ at iS
      have new1 := ih X B iS
      have new2 : A ∈ ffld T := by
        unfold ffld order_set
        simp only [Set.mem_setOf_eq]
        unfold is_imm_succ at iIS
        refine ⟨iIS.1, ?_⟩
        rcases iIS.2 with ⟨Y, hYB, hY1eq, hY2eq⟩
        use Y
        refine ⟨hYB, ?_⟩
        right
        exact hY2eq
      constructor
      · exact new2
      · exact new1.2

theorem SP4 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  valid_timeline τ → (B ∈ succs A τ ↔ A ∈ preds B τ) := by
  intro T A B vT
  have tot := totality n T A B
  have irreflex := irreflexivity n T A
  constructor
  · intro hB
    have ffldmem := SP3 T B A hB
    have hyp : A ∈ ffld T ∧ B ∈ ffld T ∧ valid_timeline T := ⟨ffldmem.2, ffldmem.1, vT⟩
    have total := tot hyp
    unfold preds
    simp only [ne_eq, Set.mem_setOf_eq]
    refine ⟨ffldmem.2, ffldmem.1, ?_, ?_⟩
    have sthm1 := SP2 T A B hB
    exact sthm1
    have contra : A = B → False := by
      intro eq
      rw [eq.symm] at hB
      exact irreflex hB
    contrapose contra
    push Not
    simp only [and_true]
    exact contra
  · intro hA
    unfold preds at hA
    simp only [ne_eq, Set.mem_setOf_eq] at hA
    rcases hA with ⟨ffldA, ffldB, nsuccA, neq⟩
    have hyp : A ∈ ffld T ∧ B ∈ ffld T ∧ valid_timeline T := ⟨ffldA, ffldB, vT⟩
    have total := tot hyp
    rcases total with As | equ | Bs
    · exact False.elim (nsuccA As)
    · exact False.elim (neq equ)
    · exact Bs

theorem SP5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A B : timeline κ n),
  valid_timeline τ → (B ∈ succs A τ ↔ B ∈ preds A (inv_timeline τ)) := by
  sorry

theorem SP6 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (B : timeline κ n),
  (succs B τ) = ∅ → ∀ A ∈ ffld τ, A ∈ preds B τ := by
  sorry

theorem SP7 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (B : timeline κ n),
  (preds B τ) = ∅ → ∀ A ∈ ffld τ, A ∈ succs B τ := by
  sorry

theorem SP8 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n))
  (A : timeline κ n),
  succs A τ ∩ preds A τ = ∅ := by
  sorry





/-
!SUBT# : Theorems regarding the substraction function
SUBT0 : Every timeline minus itself is equal to the empty set
SUBT1 : Every subtraction of timelines (T - P) is equal to the inverse
        timeline of (inverse T - inverse P)
SUBT2 : The first field of a timeline given by T - P, where T is a valid timeline and P is some
        timeline (valid or invalid), is a subset of the first field of T
SUBT3 : A timeline given by (T - P), the difference of two timelines T and P, is a subset of T
SUBT4 :
-/
theorem SUBT0 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  subt τ τ = ∅ := by
  intro T
  unfold subt
  rw [Set.ext_iff]
  intro x
  constructor
  · intro hp
    dsimp at hp
    rcases hp with ⟨h1, h2⟩
    have sthm1 : x ∈ T ∨ x ∈ {S | S ≠ S} := by
      left
      exact h1
    have sthm2 : x ∉ T → x ∈ {S | S ≠ S} := by
      intro hp
      cases sthm1 with
      | inl hp_true =>
        exact absurd hp_true hp
      | inr hq_true =>
        exact hq_true
    have sthm3 := sthm2 h2
    dsimp at sthm3
    simp only [Set.mem_empty_iff_false]
    have sthm4 : x ≠ x ↔ False := by
      tauto
    have sthm5 := sthm4.mp sthm3
    exact sthm5
  · intro hhp
    dsimp
    simp at hhp

theorem SUBT1 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  subt τ ρ = inv_timeline (subt (inv_timeline τ) (inv_timeline ρ)) := by
  intro T P
  --unfold subt
  rw [Set.ext_iff]
  intro x
  have sthm1 : ∀ τ, inv_pair x ∈ τ ↔ x ∈ inv_timeline τ := by
    intro R
    exact INV0 R (inv_pair x)
  have sthm2 := sthm1 (subt (inv_timeline T) (inv_timeline P))
  unfold subt at sthm2
  unfold subt
  constructor
  · intro h1
    dsimp at h1
    rw [sthm2.symm]
    simp only [Set.mem_setOf_eq]
    rcases h1 with ⟨shp1, shp2⟩
    constructor
    · have ssthm1 := sthm1 (inv_timeline T)
      have ssthm2 := F_INV0 T
      rw [ssthm2] at ssthm1
      exact ssthm1.mpr shp1
    · have ssthm1 := sthm1 (inv_timeline P)
      have ssthm2 := F_INV0 P
      rw [ssthm2] at ssthm1
      have ssthm3 : inv_pair x ∉ inv_timeline P ↔ x ∉ P := by
        exact not_iff_not.mpr ssthm1
      exact ssthm3.mpr shp2
  · intro h2
    have sthm1 : ∀ τ, inv_pair x ∈ τ ↔ x ∈ inv_timeline τ := by
      intro R
      exact INV0 R (inv_pair x)
    have sthm2 := sthm1 (subt (inv_timeline T) (inv_timeline P))
    unfold subt at sthm2
    rw [sthm2.symm] at h2
    dsimp at h2
    dsimp
    rcases h2 with ⟨shp1, shp2⟩
    have sthm3 := sthm1 (inv_timeline T)
    have sthm4 := F_INV0 T
    rw [sthm4] at sthm3
    have sthm5 := sthm1 (inv_timeline P)
    have sthm6 := F_INV0 P
    rw [sthm6] at sthm5
    have sthm7 : inv_pair x ∉ inv_timeline P ↔ x ∉ P := by
        exact not_iff_not.mpr sthm5
    constructor
    · exact sthm3.mp shp1
    · exact sthm7.mp shp2

theorem SUBT2 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  valid_timeline τ
  → ffld (subt τ ρ) ⊆ ffld τ := by
  intro T P hT
  unfold ffld
  unfold subt
  dsimp only [Set.mem_setOf_eq]
  simp only [Prod.exists, Set.setOf_subset_setOf, and_imp, forall_exists_index]
  intro A hp1 x y hp2 hp3 hp4
  constructor
  · unfold order_set
    dsimp only [Set.mem_setOf_eq]
    exact hT
  · have sthm1 : (x, y) ∈ T ∧ (x = A ∨ y = A) := by
      constructor
      · exact hp2
      · exact hp4
    exact ⟨x, y, sthm1⟩

theorem SUBT3 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  subt τ ρ ⊆ τ := by
  simp only [Set.subset_def]
  intro T P x
  unfold subt
  simp only [Set.mem_setOf_eq]
  intro hx
  exact hx.1

theorem SUBT4 {κ : Type T} {n : ℕ} :
  ∀ (τ ρ : Set (timeline κ n × timeline κ n)),
  (valid_timeline τ ∧ valid_timeline ρ ∧ ρ ⊆ τ) →
  ∀ x ∈ ffld ρ, ∀ y ∈ ffld (subt τ ρ), y ∈ (succs x τ) := by
  intro T P h x fx y fsy
  rcases h with ⟨vT, vP, subPT⟩
  simp only [Set.subset_def] at subPT
  simp at subPT

theorem SUBT5 {κ : Type T} {n : ℕ} :
  ∀ (τ : Set (timeline κ n × timeline κ n)),
  ordered τ →
  ∀ (ρ : Set (timeline κ n × timeline κ n)),
  (ρ ⊆ τ ∧ ordered ρ ∧ ρ ≠ τ) → ordered (subt τ ρ) := by
  intro T
  unfold ordered
  intro hVT P hP
  rcases hP with ⟨hSP, hVP, hNP⟩
  rcases hVP with hVP1 | hVP2
  simp only [Set.subset_def] at hSP
  unfold single at hVP1
  rcases hVP1 with ⟨hVP11, hVP12⟩
  have sthm1 : T.Nonempty := by
    have ssthm1 : ∃ p, p ∈ P := by
      rw [Set.nonempty_def] at hVP11
      exact hVP11
    rcases ssthm1 with ⟨p, hp⟩
    have ssthm2 := hSP p hp
    exact ⟨p, ssthm2⟩
  have sthm2 : ∃ x, x ∉ P ∧ x ∈ T := by
    simp only [ne_eq, Set.ext_iff] at hNP
    push Not at hNP
    rcases hNP with ⟨x, hx⟩
    rcases hx with hx1 | hx2
    rcases hx1 with ⟨hx11, hx12⟩
    have sssthm1 := hSP x hx11
    exact (hx12 sssthm1).elim
    exact ⟨x, hx2⟩
  have sthm3 : (subt T P).Nonempty := by
    unfold subt
    rw [Set.nonempty_def]
    simp only [Set.mem_setOf_eq]
    rcases sthm2 with ⟨x, hx⟩
    use x
    exact hx.symm
  have sthm4 := SUBT3 T P
  right
  intro hS x hx





/-
!DIST# : Theorems regarding the distance function
DIST0 - The distance between A and A in a timeline T is 0
DIST1 - The distance function is symmetric
DIST2 - The distance between A and B in T is the same as in inv_timeline T
-/
theorem DIST0 {κ : Type T} (k n : ℕ) (A : timeline κ (k + n)) :
  ∀ (τ : Set (timeline κ (k + n) × timeline κ (k + n))),
  tdist k n A A τ = 0 := by
  unfold tdist
  intro T
  unfold fld
  sorry

theorem DIST1 {κ : Type T} (k n : ℕ) (A B : timeline κ (k + n)) :
  ∀ (τ : Set (timeline κ (k + n) × timeline κ (k + n))),
  tdist k n B A τ = tdist k n A B τ := by
  sorry
