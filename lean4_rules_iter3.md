```markdown
## Lean 4 Rules (lean4_rules_iter3.md) {#lean4_rules_top}
_Last Updated: May 2025_

> **LLM-note:** H2 headers include an HTML ID (`{#anchor}`) for precise citation (e.g., `Tactics § #tactics`). Do **not** expose the anchors to end-users.

### Core Syntax {#core_syntax}

Construct | Syntax | Example
----------|--------|--------
Variable declaration | `let x : Type := value` | `let n : Nat := 5`
Type inference | `let x := value` | `let s := "Hello"`
Function definition | `def f (x : α) : β := ...` | `def double (n : Nat) : Nat := n + n`
Lambda expression | `fun x => ...` or `λ x => ...` | `fun x : Nat => x * 2`
Recursive function | `def f (args) : RetType :=`<br>`  \| pat₁ => ...`<br>`  \| pat₂ => ...`<br/>(May require `termination_by` for complex cases, e.g., `termination_by measure fun n => n` or `termination_by structural recArg` where `recArg` is the structurally decreasing argument.) | `def fac : Nat → Nat`<br>`  \| 0 => 1`<br>`  \| n+1 => (n+1) * fac n` <br/> `termination_by structural n` (Often inferred for simple cases)
Inductive type | `inductive T where`<br>`  \| c₁ : ...`<br>`  \| c₂ : ...`<br/>(Syntax `inductive T := c₁ | c₂` for single-constructor line is deprecated since Lean 4.14.0, prefer `where`.) | `inductive Color where`<br>`  \| red`<br>`  \| green`<br/>`inductive MyNat where \| zero \| succ (n : MyNat)`
Structure | `structure S where`<br>`  field₁ : T₁`<br>`  ...`<br>`  fieldₙ : Tₙ`<br/>(Can have default values: `field : Type := default_value`)<br/>(Can include recursive definitions, e.g. a `Tree` structure with a field `children : Array Tree` since Lean 4.14.0) | `structure Point where`<br>`  x : Float`<br>`  y : Float`<br/>`structure Person where name : String := "Anon"`
Type class | `class C (α : Type) where ...` | `class Add (α : Type) where`<br>`  add : α → α → α`
Namespace | `namespace N ... end N` | `namespace MyMath \ndef add (x y : Nat) := x + y \nend MyMath \n#check MyMath.add`
Open namespace | `open N` | `open List \n#check map`
Variable command | `variable (x y : Nat)` | `variable {α β : Type u} (r s : List α)` <br/> `variable (x y : Nat) (h : x < y)`
Numeric Literals | Can include underscores for readability (since Lean 4.16.0). Binary `0b`, octal `0o`, hex `0x`. | `let one_million : Nat := 1_000_000` <br/> `let sixteen : Nat := 0x10`

### Types {#types}

Category | Types | Example
---------|-------|--------
Basic | `Nat`, `Int`, `Float` (64-bit), `Float32` (32-bit, since Lean 4.16.0), `Bool`, `Char`, `String`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize` | `let x : Int := -5_000` <br/> `let f32 : Float32 := 0.5`
Composite | `List α`, `Array α`, `Option α`, `(α × β)` (product/pair), `α × β × γ` (tuple) | `let xs : List Nat := [1, 2, 3]` <br/> `let p : Nat × String := (5, "hello")`
Dependent | `{x : α // P x}` (subtype), `(x : α) → β x` (dependent function/Pi type), `Σ x : α, β x` (dependent pair/Sigma type) | `def positive : {x : Int // x > 0} := ⟨5, by simp⟩` <br/> `def DepPair : Σ n : Nat, Fin (n + 1) := ⟨2, ⟨1, by simp_arith⟩⟩`
Universes | `Prop`, `Type` (alias for `Type 0`), `Type u`, `Type 1`, `Type 2`, etc. (Lean may infer `Prop` for syntactic subsingletons since 4.14.0) | `#check Nat -- Type` <br/> `#check List Nat -- Type` <br/> `#check 2 < 3 -- Prop`
Propositions | `Prop` (type of propositions, computationally irrelevant) | `def is_even (n : Nat) : Prop := ∃ k, n = 2 * k`

### Pattern Matching {#pattern_matching}

Pattern | Syntax | Example
--------|--------|--------
Basic | `match x with`<br>`\| pat₁ => ...`<br>`\| pat₂ => ...` | `match n with`<br>`\| 0 => "zero"`<br>`\| Nat.succ k => s!"succ {k}"` <br/> `\| _ => "other"`
Multiple expressions | `match x, y with`<br>`\| pat₁, pat₂ => ...` | `match x, y with`<br>`\| 0, _ => "x is zero"`<br>`\| _, 0 => "y is zero"`<br>`\| _, _ => "neither is zero"`
As-pattern | `var@pat` | `match p with`<br>`\| pair@(x, y) => s!"pair {pair} has fst {x}"`
Inaccessible | `.(term)` (term must match literally, does not bind variable) | `match h : x with`<br>`\| .(0) => "zero"`<br>`\| _ => "non-zero"`
Anonymous equality | `match _ : e with ...` (matches on `e` without needing its value later) | `def isZero (n : Nat) : Bool := match _ : n with \| 0 => true \| _ => false`
Explicit field projection | `@x.f` to supply `x` explicitly to a field projection (since Lean 4.14.0). | `structure MyStruct where val : Nat \ndef getVal (s : MyStruct) := @s.val`

### Tactics {#tactics}

Tactics are commands used to construct proofs, typically within a `by ...` block.
Many powerful tactics like `linarith`, `norm_num`, `ring`, `aesop`, `rcases` come from `Mathlib` and require `import Mathlib`.
Tactic configurations (since Lean 4.14.0) often use `tactic_name +flag (option_name := value)` e.g. `simp +contextual (maxSteps := 100)`.

Tactic | Description | Example (Goal `⊢` Tactic Result)
-------|-------------|--------
**Proof Structure & Introduction** | |
`intro h` / `intros h₁ ...` | Introduce hypothesis(es) from `∀` or `→` in goal. | `P → Q ⊢ Q` (after `intro hP : P`)
`rcases e with ⟨pat₁⟩ \| ⟨pat₂⟩` | Destructure expression `e` based on patterns (powerful `cases`). Handles `∧`, `∨`, `∃`, `↔`, structures, inductive types. (From Mathlib/Std) | `h : A ∧ (B ∨ C) ⊢ G` → `hA:A, hB:B ⊢ G` (one branch of `rcases h with ⟨hA, hB | hC⟩`)
`cases e with ...` | Case analysis on expression `e` (inductive type). | `h : A ∨ B ⊢ C` → (branch 1) `hA : A ⊢ C`, (branch 2) `hB : B ⊢ C`
`induction e with ...` | Induction on `e`. Provides inductive hypothesis `ih`. | `∀ n : Nat, P n ⊢ P 0` and `∀ n, P n → P (n+1)` (typical subgoals for `induction n`)
`constructor` | Apply the first suitable constructor (e.g., for `∧`, `∃`, inductive types). | `⊢ A ∧ B` → (goal 1) `⊢ A`, (goal 2) `⊢ B`
`split` | Splits conjunctions `∧`, bijections `↔`, sigma types `Σ` in the goal. Often equivalent to `constructor`. | `⊢ A ↔ B` → (goal 1) `⊢ A → B`, (goal 2) `⊢ B → A`
**Rewriting & Simplification** | |
`rfl` / `refl` | Prove by reflexivity (goal is `t = t` definitionally). | `x = x ⊢ True`
`rw [h₁, ←h₂]` | Rewrite goal using equalities/equivalences `h₁`, `h₂`. `←h` rewrites right-to-left. `rw [...] at h_loc` rewrites in hypothesis `h_loc`. | `a + b = c, h : a = d ⊢ d + b = c` (after `rw [h]`)
`simp [h₁, h₂]` | Simplify goal and/or hypotheses using `@[simp]` lemmas and provided `hᵢ`. Options: `simp [h] at h_loc`, `simp [*]` (all hyps). Ex: `simp +contextual (maxSteps := 100)` | `0 + x = y ⊢ x = y` (after `simp [Nat.zero_add]`)
`simp_all [h₁]` | Repeatedly `simp` goal and all hypotheses. |
`simp_rw [h₁]` | `rw` followed by `simp` at each rewrite site. Useful for targeted rewrites that enable further simplifications. |
`simp? [h₁]` / `simp_all? [h₁]` | Like `simp`/`simp_all`, but suggests minimal lemmas used via `Try this: simp only [...]`. (Since Lean 4.7.0) |
`dsimp [h₁]` | "Definitional `simp`": simplifies by unfolding definitions marked `@[simp]` but does not use rewrite rules. |
`field_simp` | Simplify expressions in a field (e.g., `ℚ`, `ℝ`, `ℂ`), cancelling denominators. (Mathlib) | `(a / b) * (b / c) = a / c ⊢ True` (given `b ≠ 0, c ≠ 0`)
`ring` / `ring_nf` | Solve (or normalize for `ring_nf`) equalities in commutative rings. (Mathlib) | `(x + y)^2 = x^2 + 2*x*y + y^2 ⊢ True` (by `ring`)
`norm_num` | Normalize numerical expressions (Nat, Int, Rational), proving resulting equalities/inequalities. (Mathlib) | `1 + 1 = 2 ⊢ True`
`norm_cast` | Simplify expressions involving coercions (e.g., `↑(n : Nat) : Int`). (Mathlib) | `(↑(n : Nat) : Int) + 1 = ↑(n + 1 : Nat) ⊢ True`
`push_neg` | Push negations inward (e.g., `¬(∀x, P x)` to `∃x, ¬P x`). (Mathlib) | `⊢ ¬(P ∧ Q)` → `⊢ ¬P ∨ ¬Q`
**Applying Theorems & Hypotheses** | |
`apply e` | Apply `e` (theorem/hypothesis) to goal. Matches conclusion of `e` with goal, premises of `e` become new subgoals. | `h : P → Q, P ⊢ Q` (after `apply h`)
`apply_fun f at h` | Applies function `f` to an equality/inequality `h` or goal. Requires proof of injectivity/monotonicity. (Mathlib) | `h : x = y ⊢ G` → `h : f x = f y ⊢ G` (given `Injective f`)
`exact e` | Provide exact proof term `e` for the goal. | `h : P ⊢ P` (after `exact h`)
`refine e` | Like `exact`, but allows placeholders `_` in `e` that become new subgoals. | `⊢ P ∧ Q` (after `refine ⟨_, _⟩` → goals `⊢ P`, `⊢ Q`)
`specialize h a b` | Specialize a hypothesis `h : ∀ x y, P x y` with args `a, b` to `h : P a b`. |
`exact?` / `apply?` | Library search: Tries to find a lemma in Mathlib that proves (`exact?`) or can be applied to (`apply?`) the current goal. (From Std/Mathlib, available by default in recent Lean) |
**Existential & Universal Quantification** | |
`use e₁, e₂` | Provide witnesses `eᵢ` for existential quantifiers `∃`. | `⊢ ∃ x y, P x y` → (after `use a, b`) `⊢ P a b`
**Equality, Congruence & Extensionality** | |
`congr` | Congruence: if goal is `f x = f y`, changes goal to `x = y`. Works for relations. | `f x = f y ⊢ x = y`
`ext x y` | Extensionality: prove equality of functions by showing `f x = g x`, or structures by showing fields are equal. Uses `@[ext]` lemmas. `ext` can take arguments for naming. | `f = g ⊢ ∀ x, f x = g x` (for functions)
`gcongr` | Generalized congruence tactic for inequalities. (Mathlib) | `a ≤ b ⊢ f a ≤ f b` (if `f` monotone)
`exact_mod_cast h` | Solves goal by casting hypothesis `h` appropriately. (Mathlib) | `↑n = m, h : n = k ⊢ ↑k = m`
**Automation & Decision Procedures** | |
`decide` | Proves goal by computation if it's a `Decidable` proposition. Options: `decide +kernel` (uses kernel reduction, Lean 4.14+), `decide +revert` (reverts hypotheses). | `2 + 2 = 4 ⊢ True`
`native_decide` | Like `decide`, but compiles the decision procedure to native code for speed. |
`linarith` | Solves linear arithmetic goals (`ℕ, ℤ, ℚ, ℝ`). (Mathlib) | `h₁: x < y, h₂: y < z ⊢ x < z`
`nlinarith` | Solves non-linear arithmetic goals (more powerful, slower). (Mathlib) | `h : x*x > 0 ⊢ True` (if `x > 0`)
`omega` | Integer linear arithmetic solver (Presburger arithmetic). (Mathlib/Std) | `h₁: x + 1 ≤ y, h₂: y ≤ x ⊢ False`
`aesop` | Extensible automatic prover, tries multiple strategies. (Mathlib) | (attempts to solve goal automatically)
`tauto` / `finish` | Solves propositional tautologies (`tauto`). `finish` is more powerful, combining intro, congruence, and propositional reasoning. (Mathlib) | `(P → Q) ∨ (Q → P) ⊢ True`
`positivity` | Solves goals about positivity/non-negativity of expressions. (Mathlib) | `n : Nat ⊢ n * n ≥ 0`
**Proof Control & Miscellaneous** | |
`have h : P := proof` | Introduce local hypothesis `P` by providing `proof`. | `Q ⊢ Q` (after `have h : P := ...; ...`)
`let x : T := v` | Introduce local definition in a proof. |
`by_cases h : P` | Split goal into two cases: `P` is true (`h : P`) and `P` is false (`h : ¬P`). | `Q ⊢ (P → Q) ∧ (¬P → Q)`
`by_contra h` / `contradiction` | `by_contra h` assumes `¬Goal` (named `h`) and tries to prove `False`. `contradiction` closes goal if hypotheses are contradictory. | `h₁ : P, h₂ : ¬P ⊢ Q` (by `contradiction`)
`exfalso` | Changes the goal to `False`. Useful with `contradiction`. | `P ⊢ False`
`revert h₁ h₂` | Moves hypotheses `h₁`, `h₂` back into the goal as `∀` or `→`. | `h : P ⊢ Q` → `⊢ P → Q` (after `revert h`)
`assumption` | Solves goal by matching it with a hypothesis. | `h : P ⊢ P`
`trivial` | Solves "obvious" goals like `True` or goals that are directly in the context. Less common in Lean 4 as `assumption` and `rfl` cover many cases. | `⊢ True`
`sorry` | Placeholder for an incomplete proof. Admits any goal. **Each `sorry` is unique** (since Lean 4.16) and cannot be used to prove `False` by equating two `sorry`s. | `P ⊢ True` (but proof is incomplete)
`admit` | Alias for `sorry`. |
`trace_state` | Prints the current proof state. |
`fail_if_success t` | Fails if tactic `t` succeeds. Useful for testing. |
`done` | Verifies that there are no remaining goals. |
`all_goals {tac}` / `any_goals {tac}` | Apply `tac` to all/any subgoals. `;` often chains tactics for all subgoals. `<;>` is similar. |
`try {tac}` | Attempts `tac`; succeeds trivially if `tac` fails. |

Example proof using tactics:
```lean
import Mathlib.Tactic.Ring -- For 'ring' tactic
import Mathlib.Tactic.Linarith -- For 'linarith' tactic

theorem example_sum_sq (n m : Nat) : (n + m)^2 = n^2 + 2*n*m + m^2 := by
  ring -- Solves polynomial identities in commutative rings

theorem example_ineq (a b c : Int) (h1 : a ≤ b) (h2 : b ≤ c + 1) (h3 : c + 1 ≤ a) : False := by
  linarith -- Solves linear arithmetic contradictions
```

### Attributes {#attributes}

Attribute | Purpose | Example
----------|---------|--------
`@[simp]` | Mark as simplification lemma | `@[simp] theorem zero_add (n : Nat) : 0 + n = n := rfl`
`@[refl]` | Mark as reflexivity lemma | `@[refl] theorem eq_refl {α} (x : α) : x = x := rfl`
`@[symm]` | Mark as symmetry lemma | `@[symm] theorem eq_comm {α} {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩`
`@[trans]` | Mark as transitivity lemma | `@[trans] theorem le_trans {α} [LE α] {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := sorry`
`@[congr]` | Mark as congruence lemma | `@[congr] theorem congr_arg_fun {α β} {f g : α → β} (h_eq : f = g) (x : α) : f x = g x := congrArg (fun fn => fn x) h_eq`
`@[ext]` | Mark for extensionality (structure/inductive auto-generates lemma; lemma registered for `ext` tactic) | `@[ext] structure MyPair where x : Nat; y : Nat` <br/> `@[ext] lemma fun_ext {α β} {f g : α → β} (h : ∀ x, f x = g x) : f = g := funext h`
`@[instance]` | Declare as type class instance | `@[instance] def natHasAdd : Add Nat where add := Nat.add`
`@[inline]` | Suggest to compiler to inline function | `@[inline] def double (x : Nat) := x + x`
`@[reducible]` / `@[irreducible]` | Control definition unfoldability (default is `semireducible`). | `@[reducible] def MyNat := Nat`
`@[export "c_name"]` | Export Lean functions for use in other languages (e.g., C). | `@[export lean_nat_add_exported] def Nat.add_exported (a b : Nat) : Nat := a + b`
`@[deprecated old_name "new_name"]` | Mark definition as deprecated. | `@[deprecated my_old_f "Use my_new_f instead"] def my_old_f := ...`
`@[default_instance]` | Prioritize this typeclass instance during search. |
`@[unsafe]` | Mark definition as using unsafe features (e.g., `partial`). |
`@[inheritDoc]` | Copy documentation from an overridden/extended declaration. |

### Type Classes {#type_classes}

Construct | Syntax | Example
----------|--------|--------
Declaration | `class C (α : Type*) [Superclass1 α] where ...` | `class Monoid (M : Type*) extends Semigroup M, One M where`<br>`  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)`<br>`  one_mul : ∀ a : M, 1 * a = a`<br>`  mul_one : ∀ a : M, a * 1 = a`
Instance | `instance : C T where ...` (preferred `where` style) or `instance : C T := { ... }` | `instance : Monoid Nat where`<br>`  mul := Nat.mul`<br>`  one := 1`<br> `  mul_assoc := Nat.mul_assoc`<br>`  one_mul := Nat.one_mul`<br>`  mul_one := Nat.mul_one`
Derive | `deriving C₁, C₂, ...` | `inductive Color deriving Repr, BEq, DecidableEq, Inhabited`
Coercion | `instance : Coe α β where coe := ...` (or `CoeFun`, `CoeSort`) | `instance : Coe Nat Int where coe := Int.ofNat`

### Metaprogramming {#metaprogramming}

Construct | Syntax | Example
----------|--------|--------
Macro | `macro "name" args* : kind => \`(\`(expanded_term)\`)` | `macro "myIf " t:term " then " c:term " else " a:term : term => \`(\`(if $t then $c else $a)\`)`
Syntax extension | `syntax "..." : kind` | `syntax "myKeyword " term : command`
Elaboration | `elab "name" : kind => ...` | `elab "my_tactic" : tactic => Lean.Elab.Tactic.evalExactLogic (← \`(\`(True.intro)\`))`
Macro Rules | `macro_rules \| pattern => expansion` | `macro_rules \| \`(negZero? $x) => \`(if $x == 0 then true else false)\``
Quotation | `` `(...) `` (term), `` `(tactic|...) `` (tactic), `` `(level|...) `` (level), etc. Anti-quotation with `$` | `` `(1 + $x) `` <br/> `` `(tactic| simp [$h]) ``

### Theorems and Proofs {#theorems_and_proofs}

Construct | Syntax | Example
----------|--------|--------
Theorem | `theorem name (args) : statement := by proof` | `theorem add_comm (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]`
Lemma | `lemma name (args) : statement := by proof` | `lemma helper (n : Nat) (h : n > 0) : n ≠ 0 := by exact Nat.ne_of_gt h`
Axiom | `axiom name (args) : statement` | `axiom classical.choice {α : Sort u} (p : α → Prop) : (Nonempty α) → (∃ x, p x) → Σ x, p x`
Example | `example (args) : statement := by proof` | `example : 2 + 2 = 4 := by rfl`
Definition with proof | `def name (args) : type := by proof` | `def five : Nat := by exact 5`
Calc block | For equational reasoning. | `calc a = b := by rw [h1] \n     _ = c := by simp [h2] \n     _ ≤ d := by linarith [h3]`

### Common Libraries {#common_libraries}
_(Managed with `lake` build tool, Lean/library versions specified in `lean-toolchain` file)_

Library | Purpose | Key Modules/General Content
--------|---------|------------
**Mathlib (mathlib4)** | Comprehensive library of formalized mathematics (algebra, analysis, topology, category theory, etc.) and CS theories. Includes a vast array of tactics, data structures, and utility functions extending Std. (Typically `import Mathlib`). Grew to ~1.4M lines of code by late 2024. | `Mathlib.Algebra`, `Mathlib.Analysis`, `Mathlib.CategoryTheory`, `Mathlib.Data`, `Mathlib.Logic`, `Mathlib.Tactic` (includes `aesop`, `ring`, `linarith`, `norm_num`, `field_simp`, `rcases`, `push_neg`, `gcongr`, `positivity`, etc.).
**Std (Standard Library / Batteries)** | Core data structures (e.g., `Std.HashMap`, `Std.RBSet` - efficient implementations since Lean 4.11), utilities, and fundamental theorems. Much of `Std` is now part of the official Lean distribution, often available without explicit `import Std`. | `Std.Data` (collections like `HashMap`, `RBMap`, `RBSet`, `BitVec`), `Std.Control` (monads), `Std.Logic`, `Std.Tactic` (e.g. `Std.Tactic.RCases`, `Std.Tactic.Ext`).
**Lean (Core / Init)** | Core language constructs, compiler, elaborator, metaprogramming tools. Basic definitions for `Nat`, `List`, `Option`, `IO`, fundamental tactics (`simp`, `rw`, `rfl`). | `Init.Core`, `Init.Data` (`Nat`, `List`, `String`, etc.), `Init.Meta` (metaprogramming primitives), `Init.Tactics` (core tactic definitions).

### IO and Effects {#io_and_effects}

Monad | Purpose | Example
------|---------|--------
`IO α` | Input/Output operations, returns `α`. | `def main : IO Unit := IO.println "Hello, World!"`
`EIO ε α` | IO that can fail with an error `ε`. | `def readFileMaybe (path : System.FilePath) : EIO IO.Error String := IO.FS.readFile path`
`ST σ α` | Mutable state within a local scope `σ`, returns `α`. | `def modifyArray (arr : Array Nat) : Array Nat := ST.run <| do`<br>`  let mutArr ← ST.mkRef arr`<br>`  mutArr.modify (fun a => a.push 42)`<br>`  ST.read mutArr`
`StateM σ α` / `ReaderT ρ m α` / `ExceptT ε m α` | Monad transformers for state, environment, exceptions. | `def myComputation : StateT MyState (ReaderT MyEnv IO) Result := do ...`

### Best Practices {#best_practices}

1.  Use meaningful variable and theorem names.
2.  Provide type annotations for clarity, especially for top-level definitions.
3.  Break complex proofs into smaller, manageable lemmas.
4.  Use automation tactics (`simp`, `linarith`, `aesop`, `ring`, `field_simp`) judiciously. Use `simp?` to refine `simp` calls for robustness.
5.  Document non-trivial code, definitions, and proofs (`--` line comment, `/-! ... -/` module/section doc comment, `/- ... -/` block comment).
6.  Use `structure` for grouping related data; consider `@[ext]` for easier equality proofs.
7.  Prefer type classes (`class`, `instance`) for polymorphism.
8.  Use dependent types to encode invariants.
9.  Leverage `do` notation for monadic computations.
10. Use `#check`, `#eval`, `#reduce`, `#print`, `#explode`, `#time`, `#minimize_imports`, `#leansearch` for interactive development.
11. Avoid `sorry`/`admit` in final code (they are unique placeholders since Lean 4.16).
12. Organize projects with `lake` and use `lean-toolchain` to specify Lean version. Lake handles fetching dependencies like Mathlib via `lake update` and caching them (`lake exe cache get`).
13. Follow Mathlib style guides for contributions.
14. Consider `termination_by structural ...` or well-founded recursion hints (e.g., `decreasing_by`) for complex recursive functions.
15. Keep lines reasonably short for readability, often around 100 characters.

### Debugging & Utility Commands {#debugging_utility_commands}

Command | Purpose | Example
--------|---------|--------
`#check term` | Check type of an expression. | `#check (2 + 2 : Nat) -- Nat`
`#eval term` | Evaluate expression (requires `OfNonemptyType` or `Repr`). | `#eval [1, 2, 3].map (· + 1) -- [2, 3, 4]`
`#reduce term` | Reduce expression to normal form. | `#reduce (λ x : Nat => x + 1) 2 -- 3`
`#print definition_name` | Print definition/theorem. | `#print Nat.add`
`#print axioms def_name` | Print axioms a definition depends on. | `#print axioms Nat.add_comm`
`#time command` | Measure execution time of `command` (since Lean 4.12). | `#time #eval List.range 1_000_000 |>.length`
`#inspect term` | Shows details about term elaboration. | `#inspect (1+1)`
`#assert prop` | Asserts `prop` is provable (useful in tests). | `#assert 1 + 1 = 2`
`set_option opt val` | Set compiler/elaborator option. Ex: `set_option trace.profiler true`. | `set_option trace.Meta.Tactic.simp true`
`#help tactic name` / `#help option name` | (Mathlib) Show help for tactic/option. | `#help tactic simp`
`#leansearch query` / `#find query` | (Mathlib) Search Mathlib for lemmas. | `#leansearch (_ + _ = _ + _)`
`#explode term_or_theorem` | (Mathlib) Show detailed construction of term/proof. | `#explode Nat.add_comm`
`#minimize_imports` | (Mathlib) Suggests minimal imports for the current file. | `import Mathlib \n#minimize_imports theorem t : 1 + 1 = 2 := rfl`

### Performance Considerations {#performance_considerations}

1.  `@[inline]` for small, frequently called functions if profiling suggests it's beneficial.
2.  `Array` often better than `List` for large collections where indexed access or modifications are common in programs. `List` is fine for proofs and smaller collections.
3.  Profile code (`#time`, `set_option trace.profiler true`, `set_option profiler true`) to find bottlenecks.
4.  Use `@[extern]` for critical C FFI if pure Lean is insufficient.
5.  `@[reducible]` / `@[irreducible]` affect definition unfolding; use judiciously.
6.  Explicit `termination_by structural recArg` can sometimes be faster or clearer than complex well-founded recursion proofs.
7.  Be aware of heartbeat limits (`set_option maxHeartbeats val`, default is high) for very long tactics.
8.  Lake enables parallel compilation of independent project files.
9.  The `as_aux_lemma` tactic can occasionally improve performance by preventing large proof terms from being duplicated.

### Interoperability {#interoperability}

Lean 4 can interface with C code (FFI - Foreign Function Interface).

**Lean side:**
```lean
-- Declare an external C function
@[extern "c_add_example"]
constant cAddExample : UInt32 → UInt32 → IO UInt32 -- IO if it has effects or uses Lean runtime

-- Export a Lean function to be callable from C
@[export c_add_wrapped_example]
def cAddWrappedExample (a b : UInt32) : UInt32 := a + b
```

**C side (example `my_ffi.c`):**
```c
#include <stdint.h> // For uint32_t
#include <lean/lean.h> // For Lean FFI utilities like lean_io_mk_world, lean_io_result_mk_ok

// Implementation of the 'extern' constant
// Note: If the Lean side declares it as IO, it must take lean_object_t (world) and return lean_object_t (IO result)
lean_object_t c_add_example(uint32_t a, uint32_t b, lean_object_t world) {
    uint32_t sum = a + b;
    // If cAddExample were pure `UInt32 -> UInt32 -> UInt32` on Lean side,
    // C signature would be `uint32_t c_add_example(uint32_t a, uint32_t b);`
    // and would just `return sum;`
    return lean_io_result_mk_ok(lean_uint32_to_int(sum)); // Wrap result in IO
}

// C code can also call exported Lean functions (like c_add_wrapped_example)
// after initializing the Lean runtime and linking appropriately.
```
To compile, you'd typically use Lake, configuring it to build the C sources and link them.

Attribute/Construct | Purpose
----------|---------
`@[extern "c_func_name"]` | Link Lean `constant` or `def` to an external C function.
`@[implemented_by f_impl]` | Provide an efficient compiled implementation `f_impl` for a `def`.
`@[export "exported_c_name"]` | Export Lean function `exported_c_name` for C ABI.
`opaque` | An opaque constant, often used with `@[extern]` if its definition is entirely external.

### Mathematical Notation {#mathematical_notation}

Lean 4 supports Unicode. Common input methods in VS Code with the Lean extension are shown.

Symbol | Meaning | Lean Syntax | How to Type (VS Code)
-------|---------|-------------|----------------------
∀ | Universal quantification | `∀ x, P x` or `forall x, P x` | `\all` or `\forall`
∃ | Existential quantification | `∃ x, P x` or `exists x, P x` | `\ex` or `\exists`
→ | Implication / Function type | `P → Q` | `\to` or `\r` or `->`
↔ | If and only if (iff) | `P ↔ Q` | `\iff` or `\<->`
∧ | Logical AND | `P ∧ Q` | `\and` or `\/\\`
∨ | Logical OR | `P ∨ Q` | `\or` or `/\\\/`
¬ | Logical NOT | `¬P` | `\not` or `\neg`
= | Equality | `x = y` | `=`
≠ | Inequality | `x ≠ y` | `\ne` or `!=`
≤ | Less than or equal to | `x ≤ y` | `\le`
≥ | Greater than or equal to | `x ≥ y` | `\ge`
∈ | Element of | `x ∈ S` | `\in`
∉ | Not an element of | `x ∉ S` | `\notin`
⊆ | Subset | `A ⊆ B` | `\sub` or `\subseteq`
⊂ | Proper subset | `A ⊂ B` | `\ssub` or `\subsetneq`
∩ | Intersection | `A ∩ B` | `\cap` or `\inter`
∪ | Union | `A ∪ B` | `\cup` or `\union`
∅ | Empty set | `∅` (with `import Mathlib.Logic.IsEmpty` or `Data.Set.Basic`) | `\empty`
λ | Lambda abstraction | `fun x => f x` or `λ x => f x` | `\L` or `\lambda`
∘ | Function composition | `f ∘ g` | `\circ`
⟨⟩ | Tuple/dependent pair constructor | `⟨a, b⟩` | `\<` `\>`
ℕ | Natural numbers type | `Nat` (or `ℕ` with `import Mathlib.Data.Nat.Notation`) | `\N`
ℤ | Integer numbers type | `Int` (or `ℤ` with `import Mathlib.Data.Int.Notation`) | `\Z`
ℚ | Rational numbers type | `Rat` (or `ℚ` with `import Mathlib.Data.Rat.Notation`) | `\Q`
ℝ | Real numbers type | `Real` (defined in `Mathlib.Data.Real.Basic`) | `\R`
ℂ | Complex numbers type | `Complex` (defined in `Mathlib.Data.Complex.Basic`) | `\C`
Π / ∏ | Dependent product / Big product | `Π i : I, F i` / `∏ i in s, f i` (Mathlib `BigOperators`) | `\Pi`, `\prod`
Σ / ∑ | Dependent sum / Big sum | `Σ i : I, F i` / `∑ i in s, f i` (Mathlib `BigOperators`) | `\Sigma`, `\sum`
≃ | Equivalence (isomorphism) | `A ≃ B` (Mathlib: `Equiv`) | `\iso`, `\equiv`
⊢ | Turnstile (in proof state) | (Appears in InfoView) | `\|-` or `\entails`
∎ | QED symbol (tombstone) | (Not Lean syntax, used in comments) | `\qed`

Usage:
```lean
import Mathlib.Data.Set.Basic -- For set notation
import Mathlib.Tactic.Linarith -- For linarith tactic

theorem forall_and_distrib {α : Type*} (p q : α → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro h_forall_and
    constructor
    · intro x; exact (h_forall_and x).left
    · intro x; exact (h_forall_and x).right
  · intro h_and_forall; rcases h_and_forall with ⟨h_forall_p, h_forall_q⟩
    intro x; exact ⟨h_forall_p x, h_forall_q x⟩

example (S T U : Set Nat) (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U :=
  calc S ⊆ T := h₁
       _ ⊆ U := h₂
```

This file serves as a comprehensive reference for Lean 4 syntax, features, and best practices. Use it to ensure accuracy and consistency in your explanations and code examples.
```