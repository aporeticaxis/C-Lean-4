## Lean 4 Rules (lean4_rules.md)

### Core Syntax:

Construct | Syntax | Example
----------|--------|--------
Variable declaration | `let x : Type := value` | `let n : Nat := 5`
Type inference | `let x := value` | `let s := "Hello"`
Function definition | `def f (x : α) : β := ...` | `def double (n : Nat) := n + n`
Lambda expression | `fun x => ...` or `λ x => ...` | `fun x => x * 2`
Recursive function | `def f : α → β`<br>`| pat₁ => ...`<br>`| pat₂ => ...` | `def fac : Nat → Nat`<br>`| 0 => 1`<br>`| n+1 => (n+1) * fac n`
Inductive type | `inductive T where`<br>`| c₁ : ...`<br>`| c₂ : ...` | `inductive Bool where`<br>`| true`<br>`| false`
Structure | `structure S where`<br>`field₁ : T₁`<br>`...`<br>`fieldₙ : Tₙ` | `structure Point where`<br>`x : Float`<br>`y : Float`
Type class | `class C (α : Type) where ...` | `class Add (α : Type) where`<br>`add : α → α → α`

### Types:

Category | Types | Example
---------|-------|--------
Basic | `Nat`, `Int`, `Float`, `Bool`, `Char`, `String` | `let x : Int := -5`
Composite | `List α`, `Array α`, `Option α`, `(α, β)` (pairs) | `let xs : List Nat := [1, 2, 3]`
Dependent | `{x : α // P x}` (subtype), `Σ x : α, β x` (dependent pair) | `def positive : {x : Int // x > 0} := ⟨5, by simp⟩`
Universes | `Type`, `Type 1`, `Type 2`, etc. | `#check Nat -- Type`
Propositions | `Prop` | `def is_even (n : Nat) : Prop := ∃ k, n = 2 * k`

### Pattern Matching:

Pattern | Syntax | Example
--------|--------|--------
Basic | `match x with`<br>`| pat₁ => ...`<br>`| pat₂ => ...` | `match n with`<br>`| 0 => "zero"`<br>`| _ => "non-zero"`
Nested | `match x, y with`<br>`| pat₁, pat₂ => ...` | `match x, y with`<br>`| 0, _ => "x is zero"`<br>`| _, 0 => "y is zero"`<br>`| _, _ => "neither is zero"`
As-pattern | `var @ pat` | `match p with`<br>`| pair @ (x, y) => s!"pair {pair} has first component {x}"`
Inaccessible | `.(term)` | `match x with`<br>`| .(0) => "zero"`<br>`| _ => "non-zero"`

### Tactics:

Tactic | Description | Example
-------|-------------|--------
rfl | Prove by reflexivity | ``rfl : x = x ⊢ x = x``
simp | Simplify the goal | ``simp [add_comm] : a + b = c ⊢ b + a = c``
intro | Introduce variables | ``intro h : ∀ x, P x ⊢ P ?m``
apply | Apply a theorem | ``apply add_comm : a + b = c ⊢ b + a = c``
exact | Provide an exact proof term | ``exact h : h : P ⊢ P``
cases | Case analysis on an inductive type | `cases n with`<br>`| zero => ...`<br>`| succ n' => ...`
induction | Induction on an inductive type | `induction n with`<br>`| zero => ...`<br>`| succ n' ih => ...`
have | Introduce a local hypothesis | ``have h : P := proof : Q ⊢ Q``
by_cases | Split into cases | ``by_cases h : P : Q ⊢ (P → Q) ∧ (¬P → Q)``
contradiction | Prove by contradiction | ``contradiction : P, ¬P ⊢ Q``
linarith | Solve linear arithmetic | ``linarith : x + 2 < y, y ≤ x + 1 ⊢ False``

Usage:
- Tactics are used in proofs, typically after the `:= by` in theorem statements.
- Multiple tactics can be chained with `;` for sequential application.
- The `<;>` operator applies the subsequent tactic to all generated subgoals.

Example proof using tactics:
```lean
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => 
    simp
    rw [Nat.succ_add]
    rw [ih]

### Attributes:

Attribute | Purpose | Example
----------|---------|--------
@[simp] | Mark as simplification lemma | `@[simp] theorem zero_add (n : Nat) : 0 + n = n := rfl`
@[refl] | Mark as reflexivity lemma | `@[refl] theorem eq_refl {α} (x : α) : x = x := rfl`
@[symm] | Mark as symmetry lemma | `@[symm] theorem eq_comm {α} {a b : α} : a = b ↔ b = a := ⟨Eq.symm, Eq.symm⟩`
@[trans] | Mark as transitivity lemma | `@[trans] theorem le_trans {a b c : α} [LE α] : a ≤ b → b ≤ c → a ≤ c := sorry`
@[congr] | Mark as congruence lemma | `@[congr] theorem congrFun {α β} {f g : α → β} : f = g → ∀ x, f x = g x := fun h x => congrArg (· x) h`
@[ext] | Mark as extensionality lemma | `@[ext] theorem funext {α β} {f g : α → β} : (∀ x, f x = g x) → f = g := funext`
@[instance] | Declare as type class instance | `@[instance] def natHasAdd : Add Nat where add := Nat.add`
@[inline] | Inline function | `@[inline] def double (x : Nat) := x + x`
@[reducible] | Make definition reducible | `@[reducible] def Equiv (α β : Type u) := { to : α → β, inv : β → α, left_inv : ... }`

### Type Classes:

Construct | Syntax | Example
----------|--------|--------
Declaration | `class C (α : Type) where ...` | `class Monoid (α : Type) where`<br>`mul : α → α → α`<br>`one : α`
Instance | `instance : C α where ...` | `instance : Monoid Nat where`<br>`mul := Nat.mul`<br>`one := 1`
Derive | `deriving C₁, C₂, ...` | `deriving Repr, BEq, Inhabited`
Coercion | `instance : Coe α β where coe := ...` | `instance : Coe Nat Int where coe := Int.ofNat`

### Metaprogramming:

Construct | Syntax | Example
----------|--------|--------
Macro | `macro "name" : kind => ...` | `macro "myIf" t "then" c "else" a : term => `(if $t then $c else $a)`
Syntax extension | `syntax "..." : kind` | `syntax "if" term "then" term "else" term : term`
Elaboration | `elab "name" : kind => ...` | `elab "myTactic" : tactic => ...`
Quotation | `` `(...) `` | `` `(1 + 1) ``

### Theorems and Proofs:

Construct | Syntax | Example
----------|--------|--------
Theorem | `theorem name : statement := proof` | `theorem add_comm (a b : Nat) : a + b = b + a := by ...`
Lemma | `lemma name : statement := proof` | `lemma helper : P → Q := by ...`
Axiom | `axiom name : statement` | `axiom choice : ∀ {α : Type} (p : α → Prop), (∃ x, p x) → Σ x, p x`
Example | `example : statement := proof` | `example : 2 + 2 = 4 := by simp`

### Common Libraries:

Library | Purpose | Key Modules
--------|---------|------------
Mathlib | Advanced mathematics | Algebra, Topology, Measure Theory
Std | Standard library | Data (collections), Logic, Lean (core constructs)
Lean | Core Lean constructs | Elab (elaboration), Meta (metaprogramming), Parser

### IO and Effects:

Monad | Purpose | Example
------|---------|--------
IO | Input/Output operations | `def main : IO Unit := IO.println "Hello, World!"`
ST | Mutable state | `def result : Nat := ST.run <| do`<br>`let s ← ST.mkRef 0`<br>`s.modify (· + 1)`<br>`s.get`
Except | Error handling | `def safeDivide (x y : Int) : Except String Int :=`<br>`if y == 0 then .error "Division by zero" else .ok (x / y)`
Reader | Environment passing | `def result : Nat := Reader.run (do`<br>`let x ← read`<br>`pure (x + 1)`<br>`) 41`

### Best Practices:

1. Use meaningful variable names
2. Provide type annotations for clarity
3. Break complex proofs into lemmas
4. Use automation tactics judiciously
5. Document non-trivial code and proofs
6. Use structures for related data
7. Prefer type classes for polymorphic behavior
8. Use dependent types to encode invariants
9. Leverage the `do` notation for monadic computations
10. Use `#check`, `#eval`, and `#reduce` for interactive development
11. Avoid using `sorry` in final code; it should only be used as a placeholder during development

### Debugging:

Command | Purpose | Example
--------|---------|--------
#check | Check type of expression | `#check 2 + 2 -- Nat`
#eval | Evaluate expression | `#eval [1, 2, 3].map (· + 1) -- [2, 3, 4]`
#reduce | Reduce expression | `#reduce (λ x => x + 1) 2 -- 3`
#print | Print definition | `#print Nat.add`
set_option | Set compiler options | `set_option trace.Meta.Tactic.simp true`

### Performance Considerations:

1. Use `@[inline]` for small, frequently called functions
2. Prefer `Array` over `List` for large collections
3. Consider using `StateT` or `State` based on profiling results
4. Leverage type class instances for compile-time optimizations
5. Use `@[reducible]` judiciously to control reduction behavior
6. Profile your code to identify performance bottlenecks

### Interoperability:

Attribute | Purpose | Example
----------|---------|--------
@[extern] | Link to external C functions | `@[extern "lean_io_prim_put_str"] constant IO.prim.putStr : @& String → IO Unit`
@[implemented_by] | Provide efficient implementations | `@[implemented_by add_int] def add : Int → Int → Int := λ x y => x + y`
@[export] | Export Lean functions for use in other languages | `@[export lean_nat_add] def Nat.add (a b : Nat) : Nat := a + b`

### Mathematical Notation:

Symbol | Meaning | Lean Syntax
-------|---------|------------
∀ | Universal quantification | `∀ x, P x` or `∀ (x : α), P x`
∃ | Existential quantification | `∃ x, P x` or `∃ (x : α), P x`
→ | Implication | `P → Q`
↔ | If and only if | `P ↔ Q`
∧ | Logical AND | `P ∧ Q`
∨ | Logical OR | `P ∨ Q`
¬ | Logical NOT | `¬P`
= | Equality | `x = y`
≠ | Inequality | `x ≠ y`
≤ | Less than or equal to | `x ≤ y`
≥ | Greater than or equal to | `x ≥ y`
∈ | Element of | `x ∈ S`
⊆ | Subset | `A ⊆ B`
∩ | Intersection | `A ∩ B`
∪ | Union | `A ∪ B`
λ | Lambda abstraction | `λ x => f x` or `fun x => f x`

Note: Lean supports Unicode characters, which can improve the readability of code involving mathematical notation.

Usage: These symbols can be used directly in Lean code and proofs. For example:
```lean
theorem forall_and_distrib {α : Type} (p q : α → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro x; exact (h x).left
    · intro x; exact (h x).right
  · intro ⟨hp, hq⟩ x
    exact ⟨hp x, hq x⟩
```

This file serves as a comprehensive reference for Lean 4 syntax, features, and best practices. Use it to ensure accuracy and consistency in your explanations and code examples.