module

public import EvmYul.ProofTags

public section

/-!
# Toolchain upgrade check: the pure model

This module states, as checkable Lean definitions, what "the repository is fully on Lean 4.28 with a
clean version break" means, and proves the facts the audit relies on. The audit that applies these
definitions to the real repository (the files on disk, `git ls-files`, the running Lean and the
elaborated environment) is `Audits.Upgrade`, run by `lake build EvmYulGasTests`.

* **Versions.** `SemVer`, its strict order `SemVer.lt` (lexicographic on major, minor, patch), and
  `classifyVersion`, which places a parsed toolchain version as the target, older, newer, or
  unparseable. Proved: the classifier is exact (`classifyVersion_target_iff`) and its `older` /
  `newer` verdicts are correct (`classifyVersion_older`, `classifyVersion_newer`), which needs the
  trichotomy of `SemVer.lt` (`SemVer.lt_trichotomy`).
* **Readiness.** An audit produces a list of named `CheckResult`s. `cleanBreak` holds when every check
  passed; `blockers` names the failures; `passedCount` out of the list length is the progress figure.
  Proved: `cleanBreak` holds exactly when there are no blockers (`cleanBreak_iff_blockers_nil`),
  exactly when every check passed (`cleanBreak_iff_forall`), and exactly when the progress figure is
  full (`cleanBreak_iff_passedCount_eq_length`); the blocker list is sound and complete
  (`mem_blockers_iff`); one failed check is never hidden by the others (`not_cleanBreak_of_failed`).
* **Source scans.** Line-based detectors for settings a clean break forbids (`forbiddenOptionLines`)
  and for version strings left over from the old toolchain (`staleVersionLines`).
* **Module system and compiled evaluation.** A comment-aware line model (`LineView`, `codeLines`,
  `firstCode`) decides whether a file is a Lean module (`isModuleSource`) and finds proofs by
  compiled evaluation outside comments (`nativeDecideLines`). Proved: the two scanners agree
  (`firstCode_eq_head_codeLines`), the reported line is real (`firstCode_mem`), leading comments do
  not matter (`firstCode_skip_prefix`, `firstCode_closed_block`), and the specification of the
  module-system check (`checkModuleSystem_passed_iff`). Refuted: the depth-free scanner
  (`firstCodeNoDepth_disagrees`, witness `firstCode_unclosed_block`).

String functions are not evaluated by the kernel, so the string-level behaviour (`parseToolchain`,
the scanners) is checked by executed unit and property tests in the audit rather than by `decide`.
-/

namespace EvmYul.Toolchain

/-! ## Versions -/

@[expose] section

/-- A `major.minor.patch` release number. -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr, Inhabited

end

namespace SemVer

/-- `a` is an earlier release than `b` (lexicographic order on major, minor, patch). -/
@[expose] def lt (a b : SemVer) : Prop :=
  a.major < b.major ∨ (a.major = b.major ∧
    (a.minor < b.minor ∨ (a.minor = b.minor ∧ a.patch < b.patch)))

@[expose] instance (a b : SemVer) : Decidable (a.lt b) := by unfold lt; infer_instance

/-- `major.minor.patch`. -/
def render (v : SemVer) : String := s!"{v.major}.{v.minor}.{v.patch}"

theorem lt_irrefl (a : SemVer) : ¬ a.lt a := by
  unfold lt; omega

theorem lt_asymm {a b : SemVer} (h : a.lt b) : ¬ b.lt a := by
  unfold lt at *; omega

/-- Two releases are equal or ordered one way or the other. -/
theorem lt_trichotomy (a b : SemVer) : a.lt b ∨ a = b ∨ b.lt a := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  unfold lt
  simp only [mk.injEq]
  omega

end SemVer

/-- The release this repository targets. Everything else in this module is relative to it. -/
def targetVersion : SemVer := ⟨4, 28, 0⟩

/-- The prefix of a `lean-toolchain` file for an official Lean release. -/
def toolchainPrefix : String := "leanprover/lean4:v"

/-- The exact contents `lean-toolchain` must have. -/
def targetToolchain : String := toolchainPrefix ++ targetVersion.render

/-- The Mathlib tag the lakefile must require. -/
def targetMathlibTag : String := "v" ++ targetVersion.render

/-- Parse `major.minor.patch` (no prefix, no pre-release suffix). -/
def parseSemVer (s : String) : Option SemVer :=
  match s.splitOn "." with
  | [a, b, c] => do pure ⟨← a.toNat?, ← b.toNat?, ← c.toNat?⟩
  | _ => none

/-- Parse a `lean-toolchain` file: `leanprover/lean4:vX.Y.Z`, surrounding whitespace allowed.
Release candidates and nightlies are not releases and do not parse. -/
def parseToolchain (s : String) : Option SemVer :=
  let t := s.trimAscii.toString
  if t.startsWith toolchainPrefix then parseSemVer (t.drop toolchainPrefix.length).toString
  else none

@[expose] section

/-- Where a parsed toolchain version stands relative to the target. -/
inductive VersionStatus where
  | target
  | older (v : SemVer)
  | newer (v : SemVer)
  | unparseable
  deriving DecidableEq, Repr

end

/-- Classify a parse result against the target `t`. -/
def classifyVersion (t : SemVer) : Option SemVer → VersionStatus
  | none => .unparseable
  | some v => if v = t then .target else if v.lt t then .older v else .newer v

/-- The classifier reports the target exactly when the file names the target. -/
theorem classifyVersion_target_iff (t : SemVer) (p : Option SemVer) :
    classifyVersion t p = .target ↔ p = some t := by
  cases p with
  | none => simp [classifyVersion]
  | some v =>
    simp only [classifyVersion, Option.some.injEq]
    by_cases h : v = t
    · simp [h]
    · by_cases h' : v.lt t <;> simp [h, h']

/-- An `older` verdict names the parsed version, and it is strictly earlier than the target. -/
theorem classifyVersion_older {t v : SemVer} {p : Option SemVer}
    (h : classifyVersion t p = .older v) : p = some v ∧ v.lt t := by
  cases p with
  | none => simp [classifyVersion] at h
  | some w =>
    simp only [classifyVersion] at h
    by_cases h1 : w = t
    · simp [h1] at h
    · by_cases h2 : w.lt t
      · simp only [h1, h2, if_false, if_true, VersionStatus.older.injEq] at h
        subst h; exact ⟨rfl, h2⟩
      · simp [h1, h2] at h

/-- A `newer` verdict names the parsed version, and it is strictly later than the target. -/
theorem classifyVersion_newer {t v : SemVer} {p : Option SemVer}
    (h : classifyVersion t p = .newer v) : p = some v ∧ t.lt v := by
  cases p with
  | none => simp [classifyVersion] at h
  | some w =>
    simp only [classifyVersion] at h
    by_cases h1 : w = t
    · simp [h1] at h
    · by_cases h2 : w.lt t
      · simp [h1, h2] at h
      · simp only [h1, h2, if_false, VersionStatus.newer.injEq] at h
        subst h
        refine ⟨rfl, ?_⟩
        rcases SemVer.lt_trichotomy w t with h3 | h3 | h3
        · exact absurd h3 h2
        · exact absurd h3 h1
        · exact h3

/-! ## Readiness -/

@[expose] section

/-- One named check of the audit and whether it passed. -/
structure CheckResult where
  name : String
  passed : Bool
  detail : String
  deriving Repr, Inhabited

end

/-- The upgrade is complete: every check passed. -/
def cleanBreak (rs : List CheckResult) : Bool := rs.all (·.passed)

/-- The names of the checks that failed, in order. -/
def blockers (rs : List CheckResult) : List String :=
  (rs.filter (fun r => !r.passed)).map (·.name)

/-- How many checks passed. Progress is `passedCount rs` out of `rs.length`. -/
def passedCount (rs : List CheckResult) : Nat := (rs.filter (·.passed)).length

theorem cleanBreak_iff_forall (rs : List CheckResult) :
    cleanBreak rs = true ↔ ∀ r ∈ rs, r.passed = true := by
  simp [cleanBreak]

/-- The blocker list is sound and complete: a name is listed iff some check with it failed. -/
theorem mem_blockers_iff (rs : List CheckResult) (n : String) :
    n ∈ blockers rs ↔ ∃ r ∈ rs, r.passed = false ∧ r.name = n := by
  simp [blockers, and_assoc]

theorem cleanBreak_iff_blockers_nil (rs : List CheckResult) :
    cleanBreak rs = true ↔ blockers rs = [] := by
  simp [cleanBreak, blockers, List.filter_eq_nil_iff]

/-- The progress figure is full exactly when the upgrade is complete. -/
theorem cleanBreak_iff_passedCount_eq_length (rs : List CheckResult) :
    cleanBreak rs = true ↔ passedCount rs = rs.length := by
  rw [cleanBreak_iff_forall, passedCount, List.length_filter_eq_length_iff]

/-- A failed check is never hidden by the others. -/
theorem not_cleanBreak_of_failed {rs : List CheckResult} {r : CheckResult} (hr : r ∈ rs)
    (hf : r.passed = false) : cleanBreak rs = false := by
  cases h : cleanBreak rs with
  | false => rfl
  | true => simp [(cleanBreak_iff_forall rs).1 h r hr] at hf

/-! ## Source scans -/

/-- `set_option` settings that a clean break forbids in project sources: re-enabling implicit
binding, silencing the deprecation linter, downgrading warnings, or opting into `backward.*`
compatibility behaviour. -/
def forbiddenOptions : List String :=
  ["set_option autoImplicit true", "set_option relaxedAutoImplicit true",
   "set_option linter.deprecated false", "set_option warningAsError false",
   "set_option backward."]

/-- 1-based numbers of the lines of `src` that contain a forbidden setting. -/
def forbiddenOptionLines (src : String) : List Nat :=
  ((src.splitOn "\n").zipIdx 1).filterMap fun (l, i) =>
    if forbiddenOptions.any (fun o => (l.splitOn o).length > 1) then some i else none

/-- Releases this repository has left behind. -/
def retiredVersions : List String := ["4.22"]

/-- 1-based numbers of the lines that mention a retired release without also mentioning the target
(a line saying "4.22 → 4.28" is history; a line saying only "Lean 4.22" is stale). -/
def staleVersionLines (src : String) : List Nat :=
  let target := s!"{targetVersion.major}.{targetVersion.minor}"
  ((src.splitOn "\n").zipIdx 1).filterMap fun (l, i) =>
    if retiredVersions.any (fun v => (l.splitOn v).length > 1) && !((l.splitOn target).length > 1)
    then some i else none

/-- A git object id: 40 lower-case hexadecimal digits (a branch or tag name is not a pin). -/
def isFullCommit (s : String) : Bool :=
  s.length == 40 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-! ## Module headers and code lines

A Lean file is a *module* (Lean 4.28 module system) when its first line of code, outside comments,
is `module`. The scanners below work on `LineView`s, a per-line summary computed from the text by
`LineView.ofLine`; everything about comment nesting is decided on that summary, so the facts the
audit relies on are proved here, for all inputs, and the string-level summary is tested in the audit.

The model was written after a real defect: the first version of `tools/toolchain/to-module.py`
treated an `import` line *inside* a block comment as a header import. `firstCode_unclosed_block`
pins the correct behaviour and `firstCodeNoDepth_disagrees` refutes the depth-free scanner. -/

@[expose] section

/-- What the scanners need to know about one line, after trimming: its text, whether it is blank,
whether it is a line comment, whether it starts a block comment, and how many block-comment openers
`/-` and closers `-/` it contains. -/
structure LineView where
  text : String
  blank : Bool
  lineComment : Bool
  blockStart : Bool
  opens : Nat
  closes : Nat
  deriving Repr, Inhabited

end

/-- Number of (non-overlapping) occurrences of `needle` in `hay`. -/
def occurrences (hay needle : String) : Nat := (hay.splitOn needle).length - 1

/-- The summary of one source line. -/
def LineView.ofLine (l : String) : LineView :=
  let t := l.trimAscii.toString
  { text := t, blank := t.isEmpty, lineComment := t.startsWith "--",
    blockStart := t.startsWith "/-", opens := occurrences t "/-", closes := occurrences t "-/" }

/-- Block-comment depth after a line read at depth `d`. -/
def LineView.depthAfter (v : LineView) (d : Nat) : Nat := d + v.opens - v.closes

/-- Is the line skipped at depth `0` without changing the depth (blank or line comment)? -/
def LineView.skip (v : LineView) : Bool := v.blank || v.lineComment

/-- The code lines of a file, as `(line number, trimmed text)`, starting at line `n` at
block-comment depth `d`: lines inside block comments, blank lines and line comments are dropped. -/
def codeLines : Nat → Nat → List LineView → List (Nat × String)
  | _, _, [] => []
  | n, d + 1, v :: vs => codeLines (n + 1) (v.depthAfter (d + 1)) vs
  | n, 0, v :: vs =>
    if v.skip then codeLines (n + 1) 0 vs
    else if v.blockStart then codeLines (n + 1) (v.depthAfter 0) vs
    else (n, v.text) :: codeLines (n + 1) 0 vs

/-- The first code line's text, at block-comment depth `d`. -/
def firstCode : Nat → List LineView → Option String
  | _, [] => none
  | d + 1, v :: vs => firstCode (v.depthAfter (d + 1)) vs
  | 0, v :: vs =>
    if v.skip then firstCode 0 vs
    else if v.blockStart then firstCode (v.depthAfter 0) vs
    else some v.text

/-- The line views of a source text. -/
def lineViews (src : String) : List LineView := (src.splitOn "\n").map LineView.ofLine

/-- The file is a Lean module: its first code line is `module`. -/
def isModuleSource (src : String) : Bool := firstCode 0 (lineViews src) == some "module"

/-- The two scanners agree: the first code line is the head of the code lines, whatever the
starting line number. -/
theorem firstCode_eq_head_codeLines (n d : Nat) (vs : List LineView) :
    firstCode d vs = ((codeLines n d vs).head?).map Prod.snd := by
  induction vs generalizing n d with
  | nil => cases d <;> rfl
  | cons v vs ih =>
    cases d with
    | succ d => simp only [firstCode, codeLines]; exact ih _ _
    | zero =>
      simp only [firstCode, codeLines]
      split
      · exact ih _ _
      · split
        · exact ih _ _
        · rfl

/-- Soundness: a reported first code line is the text of some line of the file. -/
theorem firstCode_mem {d : Nat} {vs : List LineView} {t : String} (h : firstCode d vs = some t) :
    ∃ v ∈ vs, v.text = t := by
  induction vs generalizing d with
  | nil => cases d <;> simp [firstCode] at h
  | cons v vs ih =>
    cases d with
    | succ d =>
      obtain ⟨w, hw, rfl⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
    | zero =>
      simp only [firstCode] at h
      split at h
      · obtain ⟨w, hw, rfl⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
      · split at h
        · obtain ⟨w, hw, rfl⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
        · exact ⟨v, List.mem_cons_self, Option.some.inj h⟩

/-- Leading blank lines and line comments (a licence header, say) never change the verdict. -/
theorem firstCode_skip_prefix (cs vs : List LineView) (hcs : ∀ c ∈ cs, c.skip = true) :
    firstCode 0 (cs ++ vs) = firstCode 0 vs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, firstCode, hcs c List.mem_cons_self, if_true]
    exact ih fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')

/-- A closed one-line block comment (`/-! … -/` on one line, a docstring) is skipped. -/
theorem firstCode_closed_block (v : LineView) (vs : List LineView) (hs : v.skip = false)
    (hb : v.blockStart = true) (hc : v.opens ≤ v.closes) : firstCode 0 (v :: vs) = firstCode 0 vs := by
  simp only [firstCode, hs, hb, LineView.depthAfter, Bool.false_eq_true, if_false, if_true]
  rw [Nat.zero_add, Nat.sub_eq_zero_of_le hc]

/-- A line of code at depth `0` is the first code line. -/
theorem firstCode_code (v : LineView) (vs : List LineView) (hs : v.skip = false)
    (hb : v.blockStart = false) : firstCode 0 (v :: vs) = some v.text := by
  simp [firstCode, hs, hb]

/-- An unclosed block-comment opener. -/
def openerLine : LineView := ⟨"/-", false, false, true, 1, 0⟩

/-- A `module` line. -/
def moduleLine : LineView := ⟨"module", false, false, false, 0, 0⟩

/-- **Counterexample to the depth-free reading.** `module` inside an unclosed block comment is not a
header: such a file has no code line at all. -/
theorem firstCode_unclosed_block : firstCode 0 [openerLine, moduleLine] = none := by
  simp [firstCode, openerLine, moduleLine, LineView.skip, LineView.depthAfter]

/-- The scanner of the first `to-module.py`: it skips lines that look like comments but does not
track block-comment depth. -/
def firstCodeNoDepth : List LineView → Option String
  | [] => none
  | v :: vs => if v.skip || v.blockStart then firstCodeNoDepth vs else some v.text

/-- Negation: the depth-free scanner is not equivalent to `firstCode`; it takes the commented-out
`module` line for the header. -/
theorem firstCodeNoDepth_disagrees : ¬ ∀ vs, firstCodeNoDepth vs = firstCode 0 vs := by
  intro h
  have := h [openerLine, moduleLine]
  rw [firstCode_unclosed_block] at this
  exact absurd this (by simp [firstCodeNoDepth, openerLine, moduleLine, LineView.skip])

/-- An empty file is not a module (the check cannot pass on a missing header). -/
theorem not_isModuleSource_of_firstCode_none {src : String} (h : firstCode 0 (lineViews src) = none) :
    isModuleSource src = false := by
  simp [isModuleSource, h]

/-- Text of the code part of a line: everything before a trailing `--` comment. -/
def codePart (t : String) : String := (t.splitOn "--").headD ""

/-- Spellings of compiled evaluation in a proof (they make the proof depend on `Lean.ofReduceBool`
and trust the compiler). -/
def nativeEvalNeedles : List String := ["native_decide", "decide +native", "native := true"]

/-- 1-based numbers of the code lines (outside comments) that invoke compiled evaluation. -/
@[expose] def nativeDecideLines (src : String) : List Nat :=
  (codeLines 1 0 (lineViews src)).filterMap fun (i, t) =>
    if nativeEvalNeedles.any (fun o => occurrences (codePart t) o > 0) then some i else none

/-- Every reported line is a code line of the file (nothing inside a comment is reported). -/
theorem mem_nativeDecideLines {src : String} {i : Nat} (h : i ∈ nativeDecideLines src) :
    ∃ t, (i, t) ∈ codeLines 1 0 (lineViews src) := by
  simp only [nativeDecideLines, List.mem_filterMap] at h
  obtain ⟨⟨j, t⟩, hm, hj⟩ := h
  split at hj
  · cases hj; exact ⟨t, hm⟩
  · cases hj

/-- Lean sources that stay outside the module system, with the reason. Everything else in the
project's Lean sources must be a module (`checkModuleSystem`). -/
def legacySources : List (String × String) :=
  [("lakefile.lean", "Lake configuration, elaborated by Lake rather than imported"),
   ("Audits/Upgrade.lean",
     "reads every imported declaration (deprecation scan); a module sees imported theorems as \
      axioms without bodies"),
   ("Audits/GasAxioms.lean",
     "collects the axioms of imported theorems; inside a module imported theorems have no proofs \
      and `#print axioms` is rejected"),
   ("Audits/GasLint.lean", "runs docBlame, which needs imported docstrings (not loaded in a module)"),
   ("Audits/TestSuite.lean", "axiom and proof-term audit of every project theorem"),
   ("Audits/Layout.lean",
     "reads the source tree and the import graph of the whole library at elaboration time, like \
      the other audits"),
   ("Audits/ConjectureLedger.lean",
     "collects the axioms of the conjecture cards and reads their definition bodies; inside a module \
      imported definitions and theorems are seen without proofs"),
   ("Audits/Conjectures.lean",
     "index of an `Audits/` subfolder; `tools/repo/sync-layout.py` writes every index under `Audits/` \
      as a legacy file"),
   ("Audits.lean", "index of the audits, which are not modules (a module cannot import them)"),
   ("EvmYul/Yul/SolidityYulInterpreterTests/Main.lean",
     "imports the generated, non-module `GeneratedEvmYul` library")]

/-- The module-system check over `(path, contents)` pairs: a file is a module exactly when it is
not a listed legacy source, so a non-module file *and* a stale exception both fail it. -/
def checkModuleSystem (files : List (String × String)) : CheckResult :=
  let legacy := legacySources.map (·.1)
  let wrong := files.filter fun (f, s) => isModuleSource s == legacy.contains f
  { name := "module-system", passed := wrong.isEmpty && !files.isEmpty,
    detail := s!"{files.length} files scanned, {legacy.length} reviewed legacy sources; \
      misclassified: {wrong.map (·.1)}" }

/-- Specification of the module-system check. -/
theorem checkModuleSystem_passed_iff (files : List (String × String)) :
    (checkModuleSystem files).passed = true ↔
      files ≠ [] ∧ ∀ p ∈ files, isModuleSource p.2 = !(legacySources.map (·.1)).contains p.1 := by
  simp only [checkModuleSystem, Bool.and_eq_true, List.isEmpty_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p hp => ?_⟩
    have := h1 p hp
    cases hm : isModuleSource p.2 <;> cases hc : (legacySources.map (·.1)).contains p.1 <;>
      simp_all
  · rintro ⟨h2, h1⟩
    refine ⟨fun p hp => ?_, h2⟩
    have := h1 p hp
    cases hm : isModuleSource p.2 <;> cases hc : (legacySources.map (·.1)).contains p.1 <;>
      simp_all

/-- The compiled-evaluation check over `(path, contents)` pairs. -/
def checkNoNativeDecide (files : List (String × String)) : CheckResult :=
  let hits := files.filterMap fun (f, s) =>
    match nativeDecideLines s with | [] => none | ls => some s!"{f}:{ls}"
  { name := "no-native-decide", passed := hits.isEmpty && !files.isEmpty,
    detail := s!"{files.length} files scanned; hits: {hits}" }

/-! ### Retired representations and proof styles

`needleLines` generalises `nativeDecideLines` to any list of spellings. Two checks use it:

* `no-retired-maps`: the red-black maps and sets of Batteries and Lean core (`Batteries.RBMap`,
  `Batteries.RBSet`, `Lean.RBMap`, `Lean.RBTree`, their nodes and their modules) were replaced by
  `Std.TreeMap` / `Std.TreeSet`, whose lemma library the model's proofs use. A reintroduced
  red-black map would silently bring back a second, lemma-poor map API.
* `no-kernel-decide`: every former `decide +kernel` proof now has a `simp` or `rfl` proof. Kernel
  evaluation is sound (it adds no axiom), but it hides *why* a closed fact holds and was only
  needed to work around the elaborator's recursion limit on string comparison; a new use must
  be argued for, not slipped in. -/

/-- Fragments of the names of the retired red-black maps and sets. -/
def retiredMapNeedles : List String := ["RBMap", "RBSet", "RBTree", "RBNode"]

/-- Spellings of kernel evaluation in a proof. -/
def kernelDecideNeedles : List String := ["decide +kernel", "kernel := true"]

/-- 1-based numbers of the code lines (outside comments) that contain one of `needles`. -/
@[expose] def needleLines (needles : List String) (src : String) : List Nat :=
  (codeLines 1 0 (lineViews src)).filterMap fun (i, t) =>
    if needles.any (fun o => occurrences (codePart t) o > 0) then some i else none

/-- The compiled-evaluation scan is the needle scan for `nativeEvalNeedles`. -/
@[reviewed_rfl "restates the upgrade check's line filter"]
theorem nativeDecideLines_eq_needleLines (src : String) :
    nativeDecideLines src = needleLines nativeEvalNeedles src := rfl

/-- Every reported line is a code line of the file (nothing inside a comment is reported). -/
theorem mem_needleLines {needles : List String} {src : String} {i : Nat}
    (h : i ∈ needleLines needles src) : ∃ t, (i, t) ∈ codeLines 1 0 (lineViews src) := by
  simp only [needleLines, List.mem_filterMap] at h
  obtain ⟨⟨j, t⟩, hm, hj⟩ := h
  split at hj
  · cases hj; exact ⟨t, hm⟩
  · cases hj

/-- Scanning for no spelling at all reports nothing. -/
@[simp] theorem needleLines_nil (src : String) : needleLines [] src = [] := by
  simp [needleLines]

/-- A file-level check that no scanned file contains one of `needles` in code. -/
def checkNoNeedles (name : String) (needles : List String) (files : List (String × String)) :
    CheckResult :=
  let hits := files.filterMap fun (f, s) =>
    match needleLines needles s with | [] => none | ls => some s!"{f}:{ls}"
  { name, passed := hits.isEmpty && !files.isEmpty,
    detail := s!"{files.length} files scanned; hits: {hits}" }

/-- Specification of the needle checks: they pass exactly when something was scanned and no file
has a code line containing a needle. -/
theorem checkNoNeedles_passed_iff (name : String) (needles : List String)
    (files : List (String × String)) :
    (checkNoNeedles name needles files).passed = true ↔
      files ≠ [] ∧ ∀ p ∈ files, needleLines needles p.2 = [] := by
  simp only [checkNoNeedles, Bool.and_eq_true, List.isEmpty_iff, List.filterMap_eq_nil_iff,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p hp => ?_⟩
    have := h1 p hp
    split at this
    · assumption
    · cases this
  · rintro ⟨h2, h1⟩
    refine ⟨fun p hp => ?_, h2⟩
    split
    · rfl
    · rename_i h; exact absurd (h1 p hp) h

/-- Check 13: no red-black map or set in the project's code. -/
def checkNoRetiredMaps : List (String × String) → CheckResult :=
  checkNoNeedles "no-retired-maps" retiredMapNeedles

/-- Check 14: no kernel-evaluation proof in the project's code. -/
def checkNoKernelDecide : List (String × String) → CheckResult :=
  checkNoNeedles "no-kernel-decide" kernelDecideNeedles

end EvmYul.Toolchain
