import Switch13Reachability

/-
  Switch13Package.lean

  Standalone Lean artifact, part 3 of 3.

  This is the compact public statement.  For every odd natural number, the code
  builds the finite-state trace and proves that the trace selects one of the
  thirteen checked rows in the switch table.
-/

def ForumC17GlobalInputToSwitch13 (source : Nat) : Prop :=
  ∃ seed : C17KState,
  ∃ exitState : C17KState,
  ∃ step : Nat,
  ∃ inputA : C17Lemma1aInputA,
    c17InitialKState? source = some seed ∧
      C17KIter? seed step = some exitState ∧
      (c17L1ClassIsExit (c17L1Class (c17KBreakState exitState)) = true ∨
        C17KNext? exitState = none) ∧
      inputA.row ∈ c17Lemma1aGlobalEntryRows ∧
      (C17Lemma1aImmediateCloseoutRow inputA.row ∨
        C17Lemma1aFixedEntryRow inputA.row ∨
        C17Lemma1aFiniteLaunchMenuRow inputA.row ∨
        C17Lemma1aDownstreamCarrierRow inputA.row) ∧
      inputA.row = c17KFirstHitGlobalEntryRow (c17KBreakState exitState)

theorem forum_c17_global_input_to_switch13
    (source : Nat) (hodd : Odd source) :
    ForumC17GlobalInputToSwitch13 source := by
  obtain ⟨seed, hseed⟩ := c17_initial_kstate_total_of_odd source hodd
  obtain ⟨step, hexit⟩ :=
    c17_reachable_korbit_exits_detector
      (c17_initial_kstate_following_of_odd hodd hseed)
  obtain ⟨exitState, row, hiter, hstop, hmem, hbucket, hrow⟩ :=
    c17_kexit_witness_to_global_entry_row hexit
  exact
    ⟨seed, exitState, step, { row := row, classified := hbucket },
      hseed, hiter, hstop, hmem, hbucket, by simpa using hrow⟩

theorem forum_c17_global_input_switch13_row_mem
    (source : Nat) (hodd : Odd source) :
    ∃ inputA : C17Lemma1aInputA,
      inputA.row ∈ c17Lemma1aGlobalEntryRows ∧
        ∃ seed exitState : C17KState,
        ∃ step : Nat,
          c17InitialKState? source = some seed ∧
            C17KIter? seed step = some exitState ∧
            inputA.row =
              c17KFirstHitGlobalEntryRow (c17KBreakState exitState) := by
  obtain ⟨seed, exitState, step, inputA, hseed, hiter, hstop, hmem, hbucket, hrow⟩ :=
    forum_c17_global_input_to_switch13 source hodd
  exact ⟨inputA, hmem, seed, exitState, step, hseed, hiter, hrow⟩
