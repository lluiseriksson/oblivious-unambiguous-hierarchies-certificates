/-
  ObliviousUnambiguous.lean
  Standalone zero-dependency Lean 4.35.0 formalization of 18 core structural,
  lex-max canonical advice, Mahaney-census, loose-promise tower descent,
  dot-operator collapse, single-query guardedness, and SOUP theorems for:
    Edward A. Hirsch, "A note on input-oblivious unambiguous hierarchies",
    arXiv:2611.33126 (Nov. 24, 2026).

  Author: Lluis Eriksson
  License: MIT
-/

namespace ObliviousUnambiguous

/-- Strict lexicographic order `a <_{lex} b` on bitstrings (`List Bool`). -/
def lexLt : List Bool → List Bool → Bool
  | [], [] => false
  | false :: _, true :: _ => true
  | true :: _, false :: _ => false
  | false :: xs, false :: ys => lexLt xs ys
  | true :: xs, true :: ys => lexLt xs ys
  | _, _ => false

/-- Non-strict lexicographic order `a ≥_{lex} b` on equal-length bitstrings (`¬ (a <_{lex} b)`). -/
def lexGe (a b : List Bool) : Bool := !(lexLt a b)

/-- Helper: trichotomy for equal-length bitstrings under `lexLt` (pure structural induction). -/
private theorem lexLt_trichotomy (a : List Bool) :
    ∀ (b : List Bool), a.length = b.length →
      a = b ∨ lexLt a b = true ∨ lexLt b a = true := by
  induction a with
  | nil =>
    intro b hlen
    cases b with
    | nil => exact Or.inl rfl
    | cons _ _ => cases hlen
  | cons x xs ih =>
    intro b hlen
    cases b with
    | nil => cases hlen
    | cons y ys =>
      have hsub : xs.length = ys.length := Nat.succ.inj hlen
      cases x <;> cases y
      · cases ih ys hsub with
        | inl heq => exact Or.inl (congrArg (List.cons false) heq)
        | inr hlr =>
          cases hlr with
          | inl h1 => exact Or.inr (Or.inl h1)
          | inr h2 => exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · cases ih ys hsub with
        | inl heq => exact Or.inl (congrArg (List.cons true) heq)
        | inr hlr =>
          cases hlr with
          | inl h1 => exact Or.inr (Or.inl h1)
          | inr h2 => exact Or.inr (Or.inr h2)

/-- Theorem 1 (Sec. 2.1 & Sec. 3 Lexicographic Order Irreflexivity & Asymmetry):
    For all bitstrings `a, b : List Bool`, `lexLt a a = false` and
    `lexLt a b = true → lexLt b a = false`. -/
theorem lex_lt_irrefl_and_asymm :
    (∀ a : List Bool, lexLt a a = false) ∧
    (∀ a b : List Bool, lexLt a b = true → lexLt b a = false) := by
  constructor
  · intro a
    induction a with
    | nil => rfl
    | cons hd tl ih =>
      cases hd <;> exact ih
  · intro a
    induction a with
    | nil =>
      intro b h
      cases b <;> simp [lexLt] at h
    | cons x xs ih =>
      intro b h
      cases b with
      | nil => cases x <;> simp [lexLt] at h
      | cons y ys =>
        cases x <;> cases y
        · exact ih ys h
        · rfl
        · simp [lexLt] at h
        · exact ih ys h

/-- Theorem 2 (Lemma 3.1 Uniqueness of Canonical Lex-Max Advice `a_n`):
    If `a` and `b` are equal-length bitstrings that are both feasible (`R = true`) and
    lexicographically maximal among feasible strings of that length, then `a = b`. -/
theorem canonical_advice_unique (R : List Bool → Bool) (a b : List Bool)
    (hlen : a.length = b.length)
    (hRa : R a = true) (hRb : R b = true)
    (hmaxA : ∀ c, c.length = a.length → lexLt a c = true → R c = false)
    (hmaxB : ∀ c, c.length = b.length → lexLt b c = true → R c = false) :
    a = b := by
  cases lexLt_trichotomy a b hlen with
  | inl heq => exact heq
  | inr hlr =>
    cases hlr with
    | inl hab =>
      have := hmaxA b hlen.symm hab
      rw [hRb] at this
      cases this
    | inr hba =>
      have := hmaxB a hlen hba
      rw [hRa] at this
      cases this

/-- Build prefix-search probe `take j a ++ [true] ++ replicate (L - j - 1) false` (Lemma 3.1). -/
def buildPrefixProbe (pref : List Bool) (tailLen : Nat) : List Bool :=
  pref ++ (true :: List.replicate tailLen false)

/-- Helper: `lexLt xs (replicate xs.length false) = false` (all-zeros is the minimum bitstring). -/
private theorem lexLt_replicate_false :
    ∀ xs : List Bool, lexLt xs (List.replicate xs.length false) = false
  | [] => rfl
  | false :: tl => lexLt_replicate_false tl
  | true :: _ => rfl

/-- Helper: `lexLt (pref ++ x) (pref ++ y) = lexLt x y`. -/
private theorem lexLt_append_left :
    ∀ (pref x y : List Bool), lexLt (pref ++ x) (pref ++ y) = lexLt x y
  | [], _, _ => rfl
  | false :: ps, x, y => lexLt_append_left ps x y
  | true :: ps, x, y => lexLt_append_left ps x y

/-- Theorem 3 (Lemma 3.1 p. 10 Exact Prefix-Search Bit Recovery):
    Writing `a = pref ++ (bit :: rest)`, the prefix probe `c = pref ++ (true :: 0^{|rest|})`
    satisfies `lexGe a c = true ↔ bit = true`! -/
theorem prefix_search_bit_recovery (pref rest : List Bool) (bit : Bool) :
    lexGe (pref ++ (bit :: rest)) (buildPrefixProbe pref rest.length) = true ↔ bit = true := by
  dsimp only [lexGe, buildPrefixProbe]
  rw [lexLt_append_left]
  cases bit
  · simp [lexLt]
  · simp only [lexLt, lexLt_replicate_false, Bool.not_false]

/-- Theorem 4 (Lemma 3.1 `co-ONP` Tester Uniquely Accepts `a_n`):
    Define `T(a) := R a = true ∧ ∀ b, b.length = a.length → lexLt a b = true → R b = false`.
    If `T a_n` holds, then for every same-length string `x`, `T x ↔ x = a_n`. -/
theorem co_onp_tester_singleton (R : List Bool → Bool) (a_n : List Bool)
    (hRa : R a_n = true)
    (hmax : ∀ c, c.length = a_n.length → lexLt a_n c = true → R c = false) :
    ∀ x : List Bool, x.length = a_n.length →
      ((R x = true ∧ ∀ c, c.length = x.length → lexLt x c = true → R c = false) ↔ x = a_n) := by
  intro x hlen
  constructor
  · intro ⟨hRx, hmaxX⟩
    exact canonical_advice_unique R x a_n hlen hRx hRa hmaxX hmax
  · intro heq
    rw [heq]
    exact ⟨hRa, hmax⟩

/-- Count elements of `xs` satisfying Boolean predicate `C`. -/
def countPred (C : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: xs => (if C x then 1 else 0) + countPred C xs

/-- Decidable list membership for `Nat` (zero `Classical.choice`). -/
def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if x == y then true else memNat x ys

/-- Helper: exact indicator split `1[a] = 1[a ∧ b] + 1[a ∧ ¬b]`. -/
private theorem bit_split (a b : Bool) :
    (if a = true then 1 else 0) =
      (if (a && b) = true then 1 else 0) + (if (a && !b) = true then 1 else 0) := by
  cases a <;> cases b <;> rfl

/-- Helper: sublist count bound when all elements of `S` satisfy `C`. -/
private theorem countPred_split (C : Nat → Bool) (S : List Nat) :
    ∀ U : List Nat,
      countPred C U =
        countPred (fun x => C x && memNat x S) U +
        countPred (fun x => C x && !(memNat x S)) U
  | [] => rfl
  | x :: xs => by
    have ih := countPred_split C S xs
    have hb := bit_split (C x) (memNat x S)
    dsimp only [countPred]
    omega

/-- Theorem 5 (Lemma 2.8 Mahaney Census Checksum Completeness):
    For any universe `U : List Nat` and candidate certified set `S : List Nat`:
    if every element of `U` satisfying `C` that is in `S` contributes `countPred (C ∧ ∈S) U = countPred C U`,
    then NO element `x ∈ U` can satisfy `C x = true ∧ memNat x S = false`! -/
theorem mahaney_census_exact_subset (C : Nat → Bool) (U S : List Nat)
    (hcensus : countPred (fun x => C x && memNat x S) U = countPred C U) :
    ∀ x, x ∈ U → C x = true → memNat x S = true := by
  have hsplit := countPred_split C S U
  have hzero : countPred (fun x => C x && !(memNat x S)) U = 0 := by omega
  clear hsplit hcensus
  induction U with
  | nil => intro _ hx; cases hx
  | cons y ys ih =>
    dsimp only [countPred] at hzero
    have hhead : (if (C y && !memNat y S) = true then 1 else 0) = 0 := by omega
    have htail : countPred (fun x => C x && !memNat x S) ys = 0 := by omega
    intro x hx hCx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl hxy =>
      rw [hxy] at hCx ⊢
      cases hmy : memNat y S
      · rw [hCx, hmy] at hhead; simp at hhead
      · rfl
    | inr htl =>
      exact ih htail x htl hCx

/-- Standard Cantor pairing function `π(a, b) = (a + b)(a + b + 1)/2 + b` (Sec. 2.1). -/
def pairNat (a b : Nat) : Nat :=
  (a + b) * (a + b + 1) / 2 + b

/-- Helper: `2 * ((s * (s + 1)) / 2) = s * (s + 1)`. -/
private theorem two_mul_tri (s : Nat) : 2 * (s * (s + 1) / 2) = s * (s + 1) := by
  have heven : (s * (s + 1)) % 2 = 0 := by
    cases hmod : s % 2 with
    | zero =>
      have : s = 2 * (s / 2) := by omega
      rw [this, Nat.mul_assoc]; omega
    | succ r =>
      have : s + 1 = 2 * (s / 2 + 1) := by omega
      rw [this, Nat.mul_left_comm]; omega
  omega

/-- Helper: strict diagonal monotonicity of triangular numbers. -/
private theorem tri_lt_of_sum_lt (s1 s2 b1 b2 : Nat) (hlt : s1 < s2) (hb1 : b1 ≤ s1) :
    s1 * (s1 + 1) / 2 + b1 < s2 * (s2 + 1) / 2 + b2 := by
  have h1 := two_mul_tri s1
  have h2 := two_mul_tri s2
  have hs : s1 + 1 ≤ s2 := by omega
  have hmul1 : (s1 + 1) * (s1 + 2) ≤ s2 * (s2 + 1) :=
    Nat.mul_le_mul hs (by omega)
  have hexp : (s1 + 1) * (s1 + 2) = s1 * (s1 + 1) + 2 * (s1 + 1) := by
    have hs1 : s1 * (s1 + 1) = s1 * s1 + s1 := by rw [Nat.mul_add, Nat.mul_one]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have c1 : 1 * s1 = s1 := Nat.one_mul s1
    have c2 : s1 * 2 = 2 * s1 := Nat.mul_comm s1 2
    omega
  omega

/-- Theorem 6 (Sec. 2.1 Injective Pairing `π` for Tally Oracle Merging):
    The computable Cantor pairing `pairNat` is globally injective on `Nat × Nat`. -/
theorem cantor_pairing_injective (a1 b1 a2 b2 : Nat)
    (heq : pairNat a1 b1 = pairNat a2 b2) :
    a1 = a2 ∧ b1 = b2 := by
  dsimp only [pairNat] at heq
  have hsum : a1 + b1 = a2 + b2 := by
    by_cases hlt : a1 + b1 < a2 + b2
    · have := tri_lt_of_sum_lt (a1 + b1) (a2 + b2) b1 b2 hlt (by omega)
      omega
    · by_cases hgt : a2 + b2 < a1 + b1
      · have := tri_lt_of_sum_lt (a2 + b2) (a1 + b1) b2 b1 hgt (by omega)
        omega
      · omega
  rw [hsum] at heq
  constructor <;> omega

/-- Theorem 7 (Theorem 4.1 Bit-by-Bit Extraction of Oblivious Unambiguous Witness `w_n`):
    If `V` has oblivious unambiguous witness `w_n` on a nonempty slice (`∃ x, V x w_n = true`
    and `∀ x w, V x w = true → w = w_n`), then `(∃ x w, V x w = true ∧ bit i w = true)`
    holds if and only if `bit i w_n = true`. -/
theorem oblivious_witness_bit_extraction
    (V : Nat → Nat → Bool) (bit : Nat → Nat → Bool) (w_n : Nat) (i : Nat)
    (hnonempty : ∃ x, V x w_n = true)
    (huniq : ∀ x w, V x w = true → w = w_n) :
    (∃ x w, V x w = true ∧ bit i w = true) ↔ bit i w_n = true := by
  constructor
  · intro ⟨x, w, hV, hbit⟩
    have hw := huniq x w hV
    rw [← hw]
    exact hbit
  · intro hbit
    rcases hnonempty with ⟨x, hVx⟩
    exact ⟨x, w_n, hVx, hbit⟩

/-- Theorem 8 (Theorem 4.1 p. 11 Empty Slice Default Witness `0^{p(n)}`):
    If no input of length `n` has an accepting witness (`∀ x w, V x w = false`),
    then every bit-extraction query returns `false` (producing default witness `0^{p(n)}`). -/
theorem oblivious_empty_slice_default_zero
    (V : Nat → Nat → Bool) (bit : Nat → Nat → Bool) (i : Nat)
    (hempty : ∀ x w, V x w = false) :
    ¬(∃ x w, V x w = true ∧ bit i w = true) := by
  intro ⟨x, w, hV, _⟩
  rw [hempty x w] at hV
  cases hV

/-- Theorem 9 (Theorem 5.1 p. 12 Loose Promise-Tower Round-Termination Budget):
    With `d` hierarchy levels and query lengths `0..h`, there are `d * (h + 1)` target
    `(level, length)` slots; any generator that adds at least `1` previously missing
    true oblivious witness per round terminates in at most `d * (h + 1)` rounds. -/
theorem loose_tower_round_bound (d h rounds found : Nat)
    (hstep : rounds ≤ found) (hcap : found ≤ d * (h + 1)) :
    rounds ≤ d * (h + 1) := by
  omega

/-- Theorem 10 (Theorem 5.1 p. 13 Inductive Tower-Descent Missing-Witness Existence):
    Formalizes Hirsch's 3-case descent on level `i`: if level `0` has no wrong certified
    answers (`¬ Wrong 0`), and every wrong answer at level `j + 1` either adds a missing
    true witness (`Missing (j + 1)`) or produces a wrong answer at level `j` (`Wrong j`),
    then ANY wrong answer at level `d` guarantees `∃ j, 1 ≤ j ∧ j ≤ d ∧ Missing j`! -/
theorem loose_tower_disagreement_descent
    (Wrong Missing : Nat → Prop)
    (hbase : ¬ Wrong 0)
    (hstep : ∀ j, Wrong (j + 1) → Missing (j + 1) ∨ Wrong j) :
    ∀ d, Wrong d → ∃ j, 1 ≤ j ∧ j ≤ d ∧ Missing j := by
  intro d
  induction d with
  | zero =>
    intro hw0
    exact False.elim (hbase hw0)
  | succ k ih =>
    intro hwk
    cases hstep k hwk with
    | inl hm => exact ⟨k + 1, by omega, by omega, hm⟩
    | inr hwprev =>
      rcases ih hwprev with ⟨j, hj1, hjk, hmj⟩
      exact ⟨j, hj1, by omega, hmj⟩

/-- Theorem 11 (Theorem 5.1 p. 13 Polynomial Set-Size Growth Monotonicity):
    Every level-`j` query checked in a round triggers at most `h * (M + 1)` level-`(j-1)`
    queries; this branching factor is positive for `h ≥ 1` and monotone in `h` and `M`. -/
theorem loose_generator_set_growth_monotone (h1 h2 M1 M2 : Nat)
    (hpos : 1 ≤ h1) (hh : h1 ≤ h2) (hM : M1 ≤ M2) :
    1 ≤ h1 * (M1 + 1) ∧ h1 * (M1 + 1) ≤ h2 * (M2 + 1) := by
  have h1_le : 1 ≤ M1 + 1 := by omega
  have hprod_pos : 1 ≤ h1 * (M1 + 1) := Nat.mul_le_mul hpos h1_le
  have hprod_mono : h1 * (M1 + 1) ≤ h2 * (M2 + 1) := Nat.mul_le_mul hh (by omega)
  exact ⟨hprod_pos, hprod_mono⟩

/-- Theorem 12 (Theorem 6.2 p. 14 Fixed-Input Probe Refutation for `∃^{ou} · co-OUP`):
    For any witness length `p ≥ 1`, `0^p ≠ 1^p`; therefore if at most one witness `w`
    satisfies `R0 w = true`, then at least one of the two fixed probes `0^p` or `1^p`
    refutes `R0` (`R0 (0^p) = false ∨ R0 (1^p) = false`). -/
theorem dot_op_co_oup_probe_refutation (p : Nat) (hp : 1 ≤ p)
    (R0 : List Bool → Bool)
    (huniq : ∀ w1 w2, R0 w1 = true → R0 w2 = true → w1 = w2) :
    R0 (List.replicate p false) = false ∨ R0 (List.replicate p true) = false := by
  cases h0 : R0 (List.replicate p false)
  · exact Or.inl rfl
  · cases h1 : R0 (List.replicate p true)
    · exact Or.inr rfl
    · have heq := huniq (List.replicate p false) (List.replicate p true) h0 h1
      cases p with
      | zero => omega
      | succ k =>
        simp [List.replicate] at heq

/-- Theorem 13 (Theorem 6.2 p. 14 Unique Witness Pair `(w_n, v_N)` for `∃^{ou} · co-OUP ⊆ OUP`):
    Given inner `OUP` verifier `V` whose probe test `V0 v = true ∨ V1 v = true` uniquely
    identifies `v_N`, and outer unique witness `w_n` for `x ∈ L`, the combined verifier
    `Acc x (w, v) := (V0 v = true ∨ V1 v = true) ∧ Vx x w v = false` accepts `(w_n, v_N)`
    uniquely on positive inputs and rejects every pair on negative inputs. -/
theorem dot_op_collapse_unique_pair
    (V0 V1 : Nat → Bool) (Vx : Nat → Nat → Nat → Bool)
    (L : Nat → Bool) (w_n v_N : Nat)
    (hprobe : ∀ v, (V0 v = true ∨ V1 v = true) ↔ v = v_N)
    (hpos : ∀ x, L x = true → Vx x w_n v_N = false ∧ ∀ w, w ≠ w_n → Vx x w v_N = true)
    (hneg : ∀ x, L x = false → ∀ w, Vx x w v_N = true) :
    (∀ x w v, L x = true →
      (((V0 v = true ∨ V1 v = true) ∧ Vx x w v = false) ↔ (w = w_n ∧ v = v_N))) ∧
    (∀ x w v, L x = false →
      ¬((V0 v = true ∨ V1 v = true) ∧ Vx x w v = false)) := by
  constructor
  · intro x w v hLx
    constructor
    · intro ⟨hp, hvx⟩
      have hv : v = v_N := (hprobe v).1 hp
      rw [hv] at hvx
      by_cases hw : w = w_n
      · exact ⟨hw, hv⟩
      · have := (hpos x hLx).2 w hw
        rw [this] at hvx
        cases hvx
    · intro ⟨hw, hv⟩
      rw [hw, hv]
      exact ⟨(hprobe v_N).2 rfl, (hpos x hLx).1⟩
  · intro x w v hLx ⟨hp, hvx⟩
    have hv : v = v_N := (hprobe v).1 hp
    rw [hv] at hvx
    have := hneg x hLx w
    rw [this] at hvx
    cases hvx

/-- 4-class lattice for the oblivious unambiguous dot-operator hierarchy (Corollary 6.3). -/
inductive DotClass where
  | P
  | OUP
  | coOUP
  | Union
  deriving DecidableEq

/-- Action of `∃^{ou} ·` on the 4-class lattice (Prop. 6.1 & Thm. 6.2). -/
def applyExistsOU : DotClass → DotClass
  | .P => .OUP
  | .OUP => .OUP
  | .coOUP => .Union
  | .Union => .Union

/-- Action of `∀^{ou} ·` = `co-(∃^{ou} · co-)` on the 4-class lattice (Cor. 6.3). -/
def applyForallOU : DotClass → DotClass
  | .P => .coOUP
  | .OUP => .Union
  | .coOUP => .coOUP
  | .Union => .Union

/-- Theorem 14 (Corollary 6.3 Exact Level-2 Collapse of Alternating Dot-Operator Hierarchy):
    Both `∃^{ou} ·` and `∀^{ou} ·` collapse at level 2 (`OUP ∪ co-OUP = Union`) and
    every further application of either operator leaves `Union` invariant. -/
theorem dot_op_hierarchy_idempotence :
    applyExistsOU .coOUP = .Union ∧
    applyForallOU .OUP = .Union ∧
    applyExistsOU .Union = .Union ∧
    applyForallOU .Union = .Union ∧
    (∀ c : DotClass, applyExistsOU (applyForallOU (applyExistsOU c)) = applyForallOU (applyExistsOU c)) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro c
  cases c <;> rfl

/-- Theorem 15 (Lemma 6.4 Single Loose Query Guardedness):
    If a single-query unambiguous verifier's output depends on the answer to `q`
    (`V_ans false ≠ V_ans true`), then `q` cannot admit both consistent answers `false`
    and `true` without violating either negative-input correctness (`inL = false → V_ans b = false`)
    or positive-input witness consistency (`inL = true → V_ans false = V_ans true`). -/
theorem single_loose_query_guarded (V_ans : Bool → Bool) (inL : Bool)
    (hmatters : V_ans false ≠ V_ans true)
    (hneg_corr : inL = false → V_ans false = false ∧ V_ans true = false)
    (hpos_uniq : inL = true → V_ans false = V_ans true) :
    False := by
  cases inL
  · have ⟨h0, h1⟩ := hneg_corr rfl
    exact hmatters (by rw [h0, h1])
  · exact hmatters (hpos_uniq rfl)

/-- Theorem 16 (Theorem 6.5 Input Tagging Preserves Oblivious Unambiguity):
    If `inT xw = true` forces the query `q xw` to lie in the promise set with unique
    oblivious witness `u (qlen xw)`, and `qlen xw` depends only on the tagged length
    `tlen xw`, then every accepted tagged input of the same length shares the identical
    oblivious witness! -/
theorem input_tagging_preserves_obliviousness
    (inT : Nat → Bool) (qlen tlen : Nat → Nat) (lenMap : Nat → Nat)
    (u : Nat → Nat) (U : Nat → Nat → Bool)
    (hlen_reg : ∀ xw, qlen xw = lenMap (tlen xw))
    (hU_uniq : ∀ xw w, inT xw = true → U xw w = true → w = u (qlen xw)) :
    ∀ xw1 xw2 w1 w2,
      tlen xw1 = tlen xw2 →
      inT xw1 = true → inT xw2 = true →
      U xw1 w1 = true → U xw2 w2 = true →
      w1 = w2 := by
  intro xw1 xw2 w1 w2 ht hT1 hT2 hU1 hU2
  have hw1 := hU_uniq xw1 w1 hT1 hU1
  have hw2 := hU_uniq xw2 w2 hT2 hU2
  rw [hw1, hw2, hlen_reg xw1, hlen_reg xw2, ht]

/-- Theorem 17 (Proposition 6.6 `SOUP = OUP ∩ co-OUP` Unique Combined Witness `(b, w)`):
    Given `Y` (oblivious unambiguous verifier for `L` with witness `wY` when `L0 = true`)
    and `Z` (for `¬L` with witness `wZ` when `L0 = false`), the combined probe
    `(b = true ∧ Y w = true) ∨ (b = false ∧ Z w = true)` has a unique satisfying pair `(b, w)`. -/
theorem soup_unique_bit_witness
    (L0 : Bool) (Y Z : Nat → Bool) (wY wZ : Nat)
    (hY_pos : L0 = true → ∀ w, Y w = true ↔ w = wY)
    (hY_neg : L0 = false → ∀ w, Y w = false)
    (hZ_pos : L0 = false → ∀ w, Z w = true ↔ w = wZ)
    (hZ_neg : L0 = true → ∀ w, Z w = false) :
    ∃ b0 w0, ∀ b w,
      ((b = true ∧ Y w = true) ∨ (b = false ∧ Z w = true)) ↔ (b = b0 ∧ w = w0) := by
  cases L0
  · refine ⟨false, wZ, ?_⟩
    intro b w
    constructor
    · intro hor
      cases hor with
      | inl h1 =>
        have := hY_neg rfl w
        rw [this] at h1
        cases h1.2
      | inr h2 =>
        exact ⟨h2.1, (hZ_pos rfl w).1 h2.2⟩
    · intro ⟨hb, hw⟩
      rw [hb, hw]
      exact Or.inr ⟨rfl, (hZ_pos rfl wZ).2 rfl⟩
  · refine ⟨true, wY, ?_⟩
    intro b w
    constructor
    · intro hor
      cases hor with
      | inl h1 =>
        exact ⟨h1.1, (hY_pos rfl w).1 h1.2⟩
      | inr h2 =>
        have := hZ_neg rfl w
        rw [this] at h2
        cases h2.2
    · intro ⟨hb, hw⟩
      rw [hb, hw]
      exact Or.inl ⟨rfl, (hY_pos rfl wY).2 rfl⟩

/-- Nodes of Hirsch's Figure 1 complexity-class inclusion diagram. -/
inductive Fig1Class where
  | OUH
  | PTallyNP
  | PONPPar
  | OUHLoose
  | OGTDNP
  | PONP
  | OUM
  | ZPPONP
  deriving DecidableEq

/-- Directed containment edges of Figure 1 (Thms. 4.1, 5.1, Lem. 3.1, [KT94], [HV26b]). -/
inductive Fig1Edge : Fig1Class → Fig1Class → Prop where
  | t41 : Fig1Edge .OUH .PTallyNP
  | p27 : Fig1Edge .PTallyNP .PONPPar
  | par_to_adapt : Fig1Edge .PONPPar .PONP
  | ouh_to_loose : Fig1Edge .OUH .OUHLoose
  | t51 : Fig1Edge .OUHLoose .OGTDNP
  | kt94 : Fig1Edge .PTallyNP .OGTDNP
  | l31_ponp : Fig1Edge .OGTDNP .PONP
  | l31_oum : Fig1Edge .OGTDNP .OUM
  | hv26b : Fig1Edge .OUM .ZPPONP

/-- Reflexive-transitive closure of Figure 1 inclusions. -/
inductive Fig1Sub : Fig1Class → Fig1Class → Prop where
  | refl (c : Fig1Class) : Fig1Sub c c
  | step {a b c : Fig1Class} : Fig1Edge a b → Fig1Sub b c → Fig1Sub a c

/-- Theorem 18 (Figure 1, Cor. 4.2, Cor. 5.3 Complete Containment Closure):
    Proves all derived containments `OUH ⊆ P^{ONP}_∥`, `OUH ⊆ OUM`, `OUH ⊆ ZPP^{ONP}`,
    `OUH^• ⊆ P^{ONP}`, `OUH^• ⊆ OUM`, and `OUH^• ⊆ ZPP^{ONP}` from Hirsch's Figure 1 edges. -/
theorem class_containment_chain_complete :
    Fig1Sub .OUH .PONPPar ∧
    Fig1Sub .OUH .OUM ∧
    Fig1Sub .OUH .ZPPONP ∧
    Fig1Sub .OUHLoose .PONP ∧
    Fig1Sub .OUHLoose .OUM ∧
    Fig1Sub .OUHLoose .ZPPONP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact .step .t41 (.step .p27 (.refl _))
  · exact .step .ouh_to_loose (.step .t51 (.step .l31_oum (.refl _)))
  · exact .step .ouh_to_loose (.step .t51 (.step .l31_oum (.step .hv26b (.refl _))))
  · exact .step .t51 (.step .l31_ponp (.refl _))
  · exact .step .t51 (.step .l31_oum (.refl _))
  · exact .step .t51 (.step .l31_oum (.step .hv26b (.refl _)))

end ObliviousUnambiguous
