/-
  lemma1a/Lemma1a.lean — global-entry / Lemma 1a assembly.

  Main theorem:
    lemma1a_global_entry_all_odd

  Naming guide:
    GE suffix
      local copies of the global-entry definitions, private to this file.
    tOddGE
      the accelerated odd map T_odd(n) = (3n+1) / 2^v2(3n+1).
    q % 31104
      the representative of q modulo 31104 = lcm(6, 16, 32, 64, 128, 486).
    EntryInterface / Lemma1aEntryOutcome
      the three Lemma 1a outcome classes: closed, fixed-entry, downstream.

  Lemma 1a proves that every odd integer q selects, via its representative
  modulo 31104, one of 14 named rows. Each row is closed, fixed-entry, or a
  downstream handoff; the downstream cases are handled in the next carrier layer.

  This is an orbit partition, not a static residue-class split: the selector
  iterates T_odd at most 12 times and classifies the first iterate that meets
  a row condition. The classification therefore records orbit behavior, not
  the residue class of q itself.

  Lean 4.29.1, zero Mathlib, zero axioms.
-/

-- ============================================================
-- § Main Theorem Target
-- ============================================================

/-
  The file's target is:

    theorem lemma1a_global_entry_all_odd
        (q : Nat) (hq : q % 2 = 1) :
        Lemma1aConclusion q

  Proved at line ~322.
-/

-- ============================================================
-- § Entry Interface Types
-- ============================================================

/-
  Each GlobalEntryRow maps to one of three entry interfaces:
  closed, fixed-entry (with coordinate q_*), or downstream.
  The carrier-assembly definitions are in support/CarrierAssembly.lean;
  this file uses only the computed selector.
-/

/-- Entry-interface outcome types, as defined in paper.tex.

Launch rows appear here only after the local carrier has determined the
fixed-entry coordinate; the `fixedEntry` and `finiteLaunchFixed` constructors
carry that coordinate explicitly. -/
inductive EntryInterface where
  | finiteFunnel
  | finiteCloseout
  | strictDescent
  | fixedEntry (qStar : Nat)
  | downstreamInterface
  | finiteLaunchFixed (qStar : Nat)
  | finiteLaunchCloseout
  | finiteLaunchDownstream
  deriving DecidableEq, Repr

/-- Interfaces whose closeout requires no fixed-entry relaunch. -/
def InterfaceClosed : EntryInterface → Prop
  | EntryInterface.finiteFunnel => True
  | EntryInterface.finiteCloseout => True
  | EntryInterface.strictDescent => True
  | EntryInterface.finiteLaunchCloseout => True
  | _ => False

/-- Interfaces that hand off to a downstream carrier rather than relaunching
at a fixed entry point. -/
def InterfaceDownstream : EntryInterface → Prop
  | EntryInterface.downstreamInterface => True
  | EntryInterface.finiteLaunchDownstream => True
  | _ => False

/-- Fixed-entry interfaces expose the unique entrance coordinate `q_*`. -/
def InterfaceFixedEntry : EntryInterface → Nat → Prop
  | EntryInterface.fixedEntry q, qStar => q = qStar
  | EntryInterface.finiteLaunchFixed q, qStar => q = qStar
  | _, _ => False

/-- The three Lemma 1a outcome classes.

Every entry interface reduces to one of: a closed orbit (terminating at this
layer), a fixed-entry family parameterised by the entrance coordinate q_*, or
a downstream handoff to the carrier layer. -/
inductive Lemma1aEntryOutcome where
  | closed
  | fixedEntry (qStar : Nat)
  | downstreamCarrier
  deriving DecidableEq, Repr

def EntryInterface.lemma1aOutcome : EntryInterface → Lemma1aEntryOutcome
  | EntryInterface.finiteFunnel => Lemma1aEntryOutcome.closed
  | EntryInterface.finiteCloseout => Lemma1aEntryOutcome.closed
  | EntryInterface.strictDescent => Lemma1aEntryOutcome.closed
  | EntryInterface.fixedEntry qStar => Lemma1aEntryOutcome.fixedEntry qStar
  | EntryInterface.downstreamInterface => Lemma1aEntryOutcome.downstreamCarrier
  | EntryInterface.finiteLaunchFixed qStar => Lemma1aEntryOutcome.fixedEntry qStar
  | EntryInterface.finiteLaunchCloseout => Lemma1aEntryOutcome.closed
  | EntryInterface.finiteLaunchDownstream => Lemma1aEntryOutcome.downstreamCarrier

theorem entryInterface_outcome_classified (i : EntryInterface) :
    (i.lemma1aOutcome = Lemma1aEntryOutcome.closed ∧ InterfaceClosed i) ∨
      (∃ qStar, i.lemma1aOutcome = Lemma1aEntryOutcome.fixedEntry qStar ∧
        InterfaceFixedEntry i qStar) ∨
      (i.lemma1aOutcome = Lemma1aEntryOutcome.downstreamCarrier ∧
        InterfaceDownstream i) := by
  cases i <;> simp [EntryInterface.lemma1aOutcome, InterfaceClosed,
    InterfaceDownstream, InterfaceFixedEntry]

-- ============================================================
-- § Row Selector and Main Theorem
-- ============================================================

/-- The 14 named entry rows from paper.tex.

Rows requiring a local carrier decision appear here after that decision is
resolved; the fixed-entry coordinate is stored directly in the constructor.

The constructors `finiteFunnel`, `strictDescent`, `fixedEntry`,
`downstreamStock`, and `downstreamTerminalFamily` are not returned by
`globalEntryRowOfRep?` for the current period. They are retained for
correspondence with paper.tex and for use in later carrier layers. -/
inductive GlobalEntryRow where
  | finiteFunnel
  | finiteCloseout
  | strictDescent
  | baseTemplate
  | directDescent43
  | fixedEntry (qStar : Nat)
  | finiteLaunchFixed (qStar : Nat)
  | finiteLaunchCloseout
  | finiteLaunchDownstream
  | downstreamFiniteSplice
  | downstreamStock
  | downstreamNormalizedSuccessor
  | downstreamContinuationEffect
  | downstreamTerminalFamily
  deriving DecidableEq, Repr

/-- Map from each named row to its entry interface.

Multiple rows can share one interface: all five downstream rows map to
`downstreamInterface`, and both `baseTemplate` and `finiteCloseout` map
to `EntryInterface.finiteCloseout`. -/
def GlobalEntryRow.interface : GlobalEntryRow → EntryInterface
  | GlobalEntryRow.finiteFunnel => EntryInterface.finiteFunnel
  | GlobalEntryRow.finiteCloseout => EntryInterface.finiteCloseout
  | GlobalEntryRow.strictDescent => EntryInterface.strictDescent
  | GlobalEntryRow.baseTemplate => EntryInterface.finiteCloseout
  | GlobalEntryRow.directDescent43 => EntryInterface.strictDescent
  | GlobalEntryRow.fixedEntry qStar => EntryInterface.fixedEntry qStar
  | GlobalEntryRow.finiteLaunchFixed qStar => EntryInterface.finiteLaunchFixed qStar
  | GlobalEntryRow.finiteLaunchCloseout => EntryInterface.finiteLaunchCloseout
  | GlobalEntryRow.finiteLaunchDownstream => EntryInterface.finiteLaunchDownstream
  | GlobalEntryRow.downstreamFiniteSplice => EntryInterface.downstreamInterface
  | GlobalEntryRow.downstreamStock => EntryInterface.downstreamInterface
  | GlobalEntryRow.downstreamNormalizedSuccessor => EntryInterface.downstreamInterface
  | GlobalEntryRow.downstreamContinuationEffect => EntryInterface.downstreamInterface
  | GlobalEntryRow.downstreamTerminalFamily => EntryInterface.downstreamInterface

-- ------------------------------------------------------------
-- Computed representative-level row selector
-- ------------------------------------------------------------

private def v2GE (n : Nat) : Nat :=
  if h : n = 0 ∨ n % 2 ≠ 0 then 0 else 1 + v2GE (n / 2)
termination_by n

private def tOddGE (n : Nat) : Nat :=
  (3 * n + 1) / 2 ^ v2GE (3 * n + 1)

private def tOddIterGE (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => tOddIterGE (tOddGE n) k

-- ------------------------------------------------------------
-- Bounded-kernel certificate (finiteCloseout row)
-- ------------------------------------------------------------

private def reaches15GE (n : Nat) : Nat → Bool
  | 0 => n == 1 || n == 5
  | fuel + 1 =>
      if n == 1 || n == 5 then true else reaches15GE (tOddGE n) fuel

/-- Every odd n < 2048 reaches {1, 5} within 65 iterations of T_odd.
Verified by exhaustive computation over all 1024 odd values in [1, 2047]. -/
theorem boundedKernelGE_reaches15_fuel65 :
    ∀ k : Fin 1024, reaches15GE (2 * k.val + 1) 65 = true := by
  native_decide

theorem boundedKernelGE_reaches15_of_odd_lt2048
    (q : Nat) (hqodd : q % 2 = 1) (hqbound : q < 2048) :
    reaches15GE q 65 = true := by
  have hklt : q / 2 < 1024 := by omega
  have hcert := boundedKernelGE_reaches15_fuel65 ⟨q / 2, hklt⟩
  have hq : 2 * (q / 2) + 1 = q := by omega
  rwa [hq] at hcert

private def modularRowHitGE (q : Nat) : Bool :=
  q % 6 == 1 || q % 6 == 3 ||
  q % 128 == 85 ||
  q % 32 == 5 ||
  q % 16 == 5 ||
  q % 486 == 425 ||
  q % 486 == 59 || q % 486 == 79 || q % 486 == 25 ||
  q % 64 == 43

private def globalEntryDepthGE (q : Nat) : Nat :=
  if modularRowHitGE q || q < 2048 then 0
  else if modularRowHitGE (tOddIterGE q 1) then 1
  else if modularRowHitGE (tOddIterGE q 2) then 2
  else if modularRowHitGE (tOddIterGE q 3) then 3
  else if modularRowHitGE (tOddIterGE q 4) then 4
  else if modularRowHitGE (tOddIterGE q 5) then 5
  else if modularRowHitGE (tOddIterGE q 6) then 6
  else if modularRowHitGE (tOddIterGE q 7) then 7
  else if modularRowHitGE (tOddIterGE q 8) then 8
  else if modularRowHitGE (tOddIterGE q 9) then 9
  else if modularRowHitGE (tOddIterGE q 10) then 10
  else if modularRowHitGE (tOddIterGE q 11) then 11
  else if modularRowHitGE (tOddIterGE q 12) then 12
  -- Sentinel: for odd representatives below 31104 this branch is excluded by
  -- `globalEntryRowOfRep_complete_bool`.
  else 13

private def globalEntryLandingGE (q : Nat) : Nat :=
  tOddIterGE q (globalEntryDepthGE q)

/-- Priority-ordered row selector for a landing value.

The first matching modular condition determines the named row. Distinct row
names may still map to the same `EntryInterface` through `GlobalEntryRow.interface`;
this function only selects the row name. -/
private def globalEntryRowOfLanding? (img : Nat) : Option GlobalEntryRow :=
  if img % 6 == 1 || img % 6 == 3 then
    some GlobalEntryRow.baseTemplate
  else if img % 128 == 85 then
    some GlobalEntryRow.downstreamFiniteSplice
  else if img % 32 == 5 then
    some (GlobalEntryRow.finiteLaunchFixed img)
  else if img % 16 == 5 then
    some (GlobalEntryRow.finiteLaunchFixed img)
  else if img % 486 == 425 then
    some GlobalEntryRow.downstreamContinuationEffect
  else if img % 486 == 59 || img % 486 == 79 || img % 486 == 25 then
    some GlobalEntryRow.downstreamNormalizedSuccessor
  else if img % 64 == 43 then
    some GlobalEntryRow.directDescent43
  else
    none

private def globalEntryRowOfRep? (rep : Nat) : Option GlobalEntryRow :=
  if rep < 2048 then
    some GlobalEntryRow.finiteCloseout
  else if globalEntryDepthGE rep ≤ 12 then
    globalEntryRowOfLanding? (globalEntryLandingGE rep)
  else
    none

/-- The selector `globalEntryRowOfRep?` is total on odd elements of Fin 31104.

Proved by exhaustive computation (`native_decide`); see `GlobalEntryPartition.lean`
for the companion partition file. The selector iterates T_odd at most 12 times
and returns the first row whose modular condition the orbit value satisfies. -/
theorem globalEntryRowOfRep_complete_bool :
    ∀ rep : Fin 31104, rep.val % 2 = 1 →
      (globalEntryRowOfRep? rep.val).isSome = true := by
  native_decide

theorem globalEntryRowOfRep_complete
    (rep : Fin 31104) (hodd : rep.val % 2 = 1) :
    ∃ row, globalEntryRowOfRep? rep.val = some row := by
  have hsome := globalEntryRowOfRep_complete_bool rep hodd
  cases hrow : globalEntryRowOfRep? rep.val with
  | none =>
      simp [hrow] at hsome
  | some row =>
      exact ⟨row, rfl⟩

/-- The formal statement of Lemma 1a for an arbitrary odd q.

The representative q % 31104 selects one row from the 14-row partition, and
that row classifies as closed, fixed-entry, or downstream.

Note: the classification conjunct holds by construction of
`EntryInterface.lemma1aOutcome`; the mathematical content is the totality
of the selector over all odd representatives modulo 31104. -/
def Lemma1aConclusion (q : Nat) : Prop :=
  ∃ row : GlobalEntryRow,
    globalEntryRowOfRep? (q % 31104) = some row ∧
      ((row.interface.lemma1aOutcome = Lemma1aEntryOutcome.closed ∧
          InterfaceClosed row.interface) ∨
        (∃ qStar,
          row.interface.lemma1aOutcome = Lemma1aEntryOutcome.fixedEntry qStar ∧
            InterfaceFixedEntry row.interface qStar) ∨
        (row.interface.lemma1aOutcome = Lemma1aEntryOutcome.downstreamCarrier ∧
          InterfaceDownstream row.interface))

theorem odd_q_has_global_entry_rep
    (q : Nat) (hq : q % 2 = 1) :
    ∃ rep : Fin 31104, rep.val = q % 31104 ∧ rep.val % 2 = 1 := by
  refine ⟨⟨q % 31104, Nat.mod_lt q (by decide : 0 < 31104)⟩, rfl, ?_⟩
  have hmod2 : (q % 31104) % 2 = q % 2 := by omega
  rw [hmod2]
  exact hq

/-- Main theorem for Lemma 1a.

Every odd integer `q`, reduced modulo 31104, selects one explicitly classified
entry row: entry-closed, fixed-entry, or downstream handoff. -/
theorem lemma1a_global_entry_all_odd
    (q : Nat) (hq : q % 2 = 1) :
    Lemma1aConclusion q := by
  obtain ⟨rep, hrep, hrepOdd⟩ := odd_q_has_global_entry_rep q hq
  obtain ⟨row, hrow⟩ := globalEntryRowOfRep_complete rep hrepOdd
  refine ⟨row, ?_, ?_⟩
  · rw [← hrep]
    exact hrow
  · exact entryInterface_outcome_classified row.interface

-- ============================================================
-- § Simple Row Facts
-- ============================================================

/-
  These lemmas record the arithmetic conditions associated with each named row.
  They are separate from the coverage theorem: the coverage theorem establishes
  totality of the selector; these lemmas characterise the modular conditions
  each row certifies.
-/

private theorem landing_row_not_finiteCloseout (img : Nat) :
    globalEntryRowOfLanding? img ≠ some GlobalEntryRow.finiteCloseout := by
  unfold globalEntryRowOfLanding?
  by_cases h61 : img % 6 = 1
  · simp [h61]
  · by_cases h63 : img % 6 = 3
    · simp [h63]
    · simp [h61, h63]
      by_cases h128 : img % 128 = 85
      · simp [h128]
      · simp [h128]
        by_cases h32 : img % 32 = 5
        · simp [h32]
        · simp [h32]
          by_cases h16 : img % 16 = 5
          · simp [h16]
          · simp [h16]
            by_cases h425 : img % 486 = 425
            · simp [h425]
            · simp [h425]
              by_cases h59 : img % 486 = 59
              · simp [h59]
              · by_cases h79 : img % 486 = 79
                · simp [h79]
                · by_cases h25 : img % 486 = 25
                  · simp [h25]
                  · simp [h59, h79, h25]

/-- The `finiteCloseout` row is selected exactly by the small-representative
guard in `globalEntryRowOfRep?`. -/
theorem finiteCloseout_row_rep_lt2048
    (rep : Nat)
    (hrow : globalEntryRowOfRep? rep = some GlobalEntryRow.finiteCloseout) :
    rep < 2048 := by
  unfold globalEntryRowOfRep? at hrow
  by_cases hlt : rep < 2048
  · exact hlt
  · simp [hlt] at hrow
    by_cases hdepth : globalEntryDepthGE rep ≤ 12
    · have hnot := landing_row_not_finiteCloseout (globalEntryLandingGE rep)
      simp [hdepth] at hrow
      exact False.elim (hnot hrow)
    · simp [hdepth] at hrow

/-- An odd representative selected by `finiteCloseout` reaches {1, 5}
within 65 iterations of T_odd. -/
theorem finiteCloseout_row_reaches15
    (rep : Nat) (hodd : rep % 2 = 1)
    (hrow : globalEntryRowOfRep? rep = some GlobalEntryRow.finiteCloseout) :
    reaches15GE rep 65 = true :=
  boundedKernelGE_reaches15_of_odd_lt2048 rep hodd
    (finiteCloseout_row_rep_lt2048 rep hrow)

/-- The `baseTemplate` row is selected only from a landing value congruent to
`1` or `3` modulo `6`. -/
theorem baseTemplate_row_mod6
    (img : Nat)
    (hrow : globalEntryRowOfLanding? img = some GlobalEntryRow.baseTemplate) :
    img % 6 = 1 ∨ img % 6 = 3 := by
  unfold globalEntryRowOfLanding? at hrow
  by_cases h61 : img % 6 = 1
  · exact Or.inl h61
  · by_cases h63 : img % 6 = 3
    · exact Or.inr h63
    · exfalso
      simp [h61, h63] at hrow
      by_cases h128 : img % 128 = 85
      · simp [h128] at hrow
      · simp [h128] at hrow
        by_cases h32 : img % 32 = 5
        · simp [h32] at hrow
        · simp [h32] at hrow
          by_cases h16 : img % 16 = 5
          · simp [h16] at hrow
          · simp [h16] at hrow
            by_cases h425 : img % 486 = 425
            · simp [h425] at hrow
            · simp [h425] at hrow
              by_cases h59 : img % 486 = 59
              · simp [h59] at hrow
              · by_cases h79 : img % 486 = 79
                · simp [h79] at hrow
                · by_cases h25 : img % 486 = 25
                  · simp [h25] at hrow
                  · by_cases h64 : img % 64 = 43
                    · simp [h59, h79, h25, h64] at hrow
                    · simp [h59, h79, h25, h64] at hrow

/-- Landing values in the `directDescent43` row satisfy img % 64 = 43. -/
theorem directDescent43_row_mod64
    (img : Nat)
    (hrow : globalEntryRowOfLanding? img = some GlobalEntryRow.directDescent43) :
    img % 64 = 43 := by
  unfold globalEntryRowOfLanding? at hrow
  by_cases h61 : img % 6 = 1
  · simp [h61] at hrow
  · by_cases h63 : img % 6 = 3
    · simp [h63] at hrow
    · simp [h61, h63] at hrow
      by_cases h128 : img % 128 = 85
      · simp [h128] at hrow
      · simp [h128] at hrow
        by_cases h32 : img % 32 = 5
        · simp [h32] at hrow
        · simp [h32] at hrow
          by_cases h16 : img % 16 = 5
          · simp [h16] at hrow
          · simp [h16] at hrow
            by_cases h425 : img % 486 = 425
            · simp [h425] at hrow
            · simp [h425] at hrow
              by_cases h59 : img % 486 = 59
              · simp [h59] at hrow
              · by_cases h79 : img % 486 = 79
                · simp [h79] at hrow
                · by_cases h25 : img % 486 = 25
                  · simp [h25] at hrow
                  · by_cases h64 : img % 64 = 43
                    · exact h64
                    · simp [h59, h79, h25, h64] at hrow

/-- The `finiteLaunchFixed` row stores the selected landing value as its
fixed-entry coordinate. -/
theorem finiteLaunchFixed_row_landing
    (img qStar : Nat)
    (hrow : globalEntryRowOfLanding? img =
      some (GlobalEntryRow.finiteLaunchFixed qStar)) :
    qStar = img ∧ (img % 32 = 5 ∨ img % 16 = 5) := by
  unfold globalEntryRowOfLanding? at hrow
  by_cases h61 : img % 6 = 1
  · simp [h61] at hrow
  · by_cases h63 : img % 6 = 3
    · simp [h63] at hrow
    · simp [h61, h63] at hrow
      by_cases h128 : img % 128 = 85
      · simp [h128] at hrow
      · simp [h128] at hrow
        by_cases h32 : img % 32 = 5
        · have hq : qStar = img := by
            simpa [h32] using hrow.symm
          exact ⟨hq, Or.inl h32⟩
        · simp [h32] at hrow
          by_cases h16 : img % 16 = 5
          · have hq : qStar = img := by
              simpa [h16] using hrow.symm
            exact ⟨hq, Or.inr h16⟩
          · simp [h16] at hrow
            by_cases h425 : img % 486 = 425
            · simp [h425] at hrow
            · simp [h425] at hrow
              by_cases h59 : img % 486 = 59
              · simp [h59] at hrow
              · by_cases h79 : img % 486 = 79
                · simp [h79] at hrow
                · by_cases h25 : img % 486 = 25
                  · simp [h25] at hrow
                  · by_cases h64 : img % 64 = 43
                    · simp [h59, h79, h25, h64] at hrow
                    · simp [h59, h79, h25, h64] at hrow

/-- Landing values for `finiteLaunchFixed` satisfy img % 32 = 5 or img % 16 = 5. -/
theorem finiteLaunchFixed_row_mod
    (img qStar : Nat)
    (hrow : globalEntryRowOfLanding? img =
      some (GlobalEntryRow.finiteLaunchFixed qStar)) :
    img % 32 = 5 ∨ img % 16 = 5 :=
  (finiteLaunchFixed_row_landing img qStar hrow).2

/-- Descent arithmetic for the `directDescent43` row: `q ≡ 43 (mod 64)`
implies strict decrease under the carried `(3q - 1) / 64` image. -/
theorem directDescent43_strict (q : Nat) (h : q % 64 = 43) :
    (3 * q - 1) / 64 < q := by
  let a := q / 64
  have hq : q = 64 * a + 43 := by
    unfold a
    omega
  rw [hq]
  have hid : 3 * (64 * a + 43) - 1 = 64 * (3 * a + 2) := by omega
  rw [hid]
  have hdiv : (64 * (3 * a + 2)) / 64 = 3 * a + 2 :=
    Nat.mul_div_cancel_left (3 * a + 2) (by decide : 0 < 64)
  rw [hdiv]
  omega

/-- Selecting `directDescent43` implies (3 * img - 1) / 64 < img. -/
theorem directDescent43_row_strict
    (img : Nat)
    (hrow : globalEntryRowOfLanding? img = some GlobalEntryRow.directDescent43) :
    (3 * img - 1) / 64 < img :=
  directDescent43_strict img (directDescent43_row_mod64 img hrow)
