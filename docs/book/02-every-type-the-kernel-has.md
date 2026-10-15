# 2. Every type the kernel has

> **Where you are.** Chapter 2 of 9 in Part I.
>
> **Before this.** [Chapter 1](01-a-proof-is-a-program.md). You need one idea
> from it: a proof is a term, and one program checks both.
>
> **This chapter adds** the five types that the whole kernel is written in.
>
> **This chapter is a map, not a lesson.** Every other chapter of Part I adds
> one idea. This one adds ten names. Read it once, go on, and come back when a
> later chapter uses a name you do not hold yet.
>
> **The four beats.** Each section gives the idea, then the data, then one
> function, then the rule. No formula arrives before the type it compresses.
> Section 2.10 is the `Try it`, and it runs the three cached numbers.

---

## 2.1 The idea

A proof checker is one function, and it runs once per declaration.

```
  a declaration ──► check ──┬──► yes. Remember it.
                            └──► no. Say why.
```

The thing it remembers is called the **environment**. The environment is a map
from a name to a declaration that the checker has already accepted. Nothing
else survives between one declaration and the next.

So the job needs five types.

| Type | What it holds |
|---|---|
| `Name` | a global identifier, such as the name of a declaration |
| `Level` | which universe a type lives in |
| `Expr` | a term: a value, a function, a type, or a proof |
| `Declaration` | one entry of the environment |
| `LocalContext` | the variables that the checker itself invented |

Four of the five are trees, and the fifth is a list. There is no graph, no
mutable node, and no back pointer anywhere in this chapter. That is the reason
a kernel stays small enough to trust.

---

## 2.2 `Name`

### The idea

A declaration needs an identifier. Three forces shape it.

- A namespace adds the same prefix to many identifiers at once.
- The front end invents identifiers of its own, and not one of them may ever
  clash with an identifier that a human wrote.
- The kernel compares identifiers on a path that runs millions of times.

A plain string loses the first force and the second one.

### The data

```ts
type Name =
  | { k: "anon" }
  | { k: "str"; prefix: Name; part: string; hash: number; parts: number }
  | { k: "num"; prefix: Name; part: number; hash: number; parts: number }
```

`anon` is the empty root of every name. `str` adds a text part. `num` adds a
number part, and that is what a generated identifier uses, so a generated
identifier can never collide with a text one.

A name grows one part at a time, and the new part wraps the old name as its
`prefix`. The identifier `Nat.add` is therefore:

```
str(str(anon, "Nat"), "add")
```

Read it from the inside out. One consequence matters: every name in a namespace
shares one prefix node, so a namespace of a thousand names stores its prefix
once.

### The code

`hash` and `parts` are computed where the part is added, and never again. So
two different names reject each other on one number.

```ts
function equal(a: Name, b: Name): boolean {
  if (a === b) return true
  if (a.k !== b.k) return false
  if (a.k === "anon") return true
  if (a.hash !== b.hash) return false
  if (a.parts !== b.parts) return false
  return a.part === b.part && equal(a.prefix, b.prefix)
}
```

The first line is the common case under a shared prefix. The `hash` line is the
common case everywhere else.

### The rule

The kernel asks a name two questions, and no others. Are these two names equal?
Which declaration does this name refer to? Both are cheap here, and that is the
only requirement.

**One design decision, and its alternative.** You can **intern** a name
instead: create each distinct name once, keep a table of every name built, and
let equality be one pointer test. This kernel does not. It caches the hash and
shares the prefix. The trade is plain. Interning buys the cheapest possible
equality, and it costs a table that lives as long as the run and that every
thread must reach. A cached hash buys a reject that is nearly as cheap, and it
costs four bytes per part.

---

## 2.3 `Level`

### The idea

Every term has a type. A type is a term, so a type has a type as well. If a
type could hold itself, the system would prove anything at all. So types live
on a ladder, and each rung of the ladder is a **universe**.

- `Sort 0` is `Prop`, the universe of propositions.
- `Sort 1` is `Type`, which holds an ordinary data type such as a number.
- `Sort 2` holds `Type`, and the ladder goes up for ever.

A **level** is the number of the rung. Two forces stop it from being a plain
number.

- One definition must work on every rung. A list of numbers and a list of lists
  use one definition, so a level can be a **variable**.
- A function type sits at least as high as its input type and its output type,
  so a level can be the **larger of two** levels, and neither one is known yet.

### The data

```ts
type Level =
  | { k: "zero" }
  | { k: "succ"; of: Level }
  | { k: "max"; a: Level; b: Level }
  | { k: "imax"; a: Level; b: Level }
  | { k: "param"; name: Name }
```

`zero` and `succ` give a concrete rung. `param` is the variable. `max` is the
larger of two. `imax` needs a paragraph of its own.

**`imax a b` is `zero` when `b` is `zero`. Otherwise it is `max a b`.** That one
exception does all the work of the bottom rung. A statement that begins "for
every type" speaks about a thing of any size, and the statement itself stays a
proposition, which is to say it stays on rung 0. Without `imax` the statement
would climb to the rung of the thing it speaks about, and a proposition about
every type would no longer be a proposition. The name of that property is
**impredicativity**.

### The code

```ts
function toNat(l: Level): number | null {
  switch (l.k) {
    case "zero":
      return 0
    case "succ": {
      const n = toNat(l.of)
      return n === null ? null : n + 1
    }
    case "max": {
      const a = toNat(l.a)
      const b = toNat(l.b)
      return a === null || b === null ? null : Math.max(a, b)
    }
    case "imax": {
      const b = toNat(l.b)
      if (b === null) return null
      if (b === 0) return 0
      const a = toNat(l.a)
      return a === null ? null : Math.max(a, b)
    }
    case "param":
      return null
  }
}
```

The `null` is the whole difficulty of the universes. A level that holds a param
has no number, so the kernel cannot compute the answer. It must decide "equal"
and "no larger than" on the symbols themselves. Chapter 5 gives that algorithm,
and the `imax` case above is the reason the algorithm has to split into cases.

### The rule

A universe is a term, because a term must be able to say `α : Sort u`. So
`Level` is not a side table. It sits inside `Expr`, and the next section shows
where.

---

## 2.4 `Expr`

### The idea

One type holds a value, a function, a type, and a proof. That is not an economy
measure. It is the claim of chapter 1, written down as data: a proof **is** a
term, so no separate type of proofs exists.

### The data

```ts
type BinderInfo = "default" | "implicit" | "strictImplicit" | "instImplicit"

type Literal = { nat: string } | { str: string }

type Expr =
  | { k: "bvar"; index: number }
  | { k: "fvar"; id: number }
  | { k: "mvar"; id: number }
  | { k: "sort"; level: Level }
  | { k: "const"; name: Name; levels: Level[] }
  | { k: "app"; fun: Expr; arg: Expr }
  | { k: "lam"; binderName: Name; binderType: Expr; body: Expr; info: BinderInfo }
  | { k: "forall"; binderName: Name; binderType: Expr; body: Expr; info: BinderInfo }
  | { k: "let"; binderName: Name; binderType: Expr; value: Expr; body: Expr }
  | { k: "lit"; lit: Literal }
  | { k: "proj"; structure: Name; index: number; value: Expr }
```

Eleven kinds. Here is what each one is for.

| Kind | What it is |
|---|---|
| `bvar` | a variable that an enclosing binder made, held as a number |
| `fvar` | a variable that the checker itself made |
| `mvar` | a hole that the front end has not filled yet |
| `sort` | the universe `Sort l` |
| `const` | a reference to a declaration, with a level for each of its universe variables |
| `app` | one function applied to one argument |
| `lam` | a function |
| `forall` | a function **type**, where the output type may speak about the input |
| `let` | a local definition |
| `lit` | a number or a text literal |
| `proj` | one field of a structure |

Six of the eleven need more than a line.

**`bvar` is a number, not a name.** The number counts binders outward. A
function that takes two arguments and returns the first is
`lam(lam(bvar 1))`. The index 1 means "skip one binder, then take that one". So
the name of a variable is never part of the meaning, and two functions that
differ only in their variable names are the identical tree. Chapter 3 is about
that one decision and what it costs.

**`fvar` never appears in the input.** The checker makes one when it goes under
a binder, and section 2.8 shows how.

**`forall` is one constructor for four things.** A plain arrow from `A` to `B`,
a dependent function type, the quantifier "for every", and logical implication
are all this one node. That is the whole of the logic, and chapter 4 earns the
claim.

**`lit` holds its digits as text.** A natural number in this system has no upper
bound, so no fixed integer type can hold every literal. The kernel parses the
text into a fixed width integer, computes, and **refuses** when a value will not
fit. A term that is too large then stays stuck. That is the right failure: a
stuck term is a wrong answer you can see, and a wrapped integer is a wrong
answer you cannot.

**`mvar` must exist in the type, and must never pass the check.** A finished
term holds no hole. So why hold one in the type at all? Because the input format
can carry one, and **a type that cannot hold the bad case cannot reject it.** A
reader that silently dropped a hole would turn a broken input into a term the
checker is happy with. So the hole survives into `Expr`, and the type checker
refuses it by name, with an error that says which hole it was.

**`proj` is a shortcut that pays for itself.** You can already read a field by
taking the structure apart with its recursor, so `proj` adds no power. It adds
speed, and it makes one rule easy to state: a pair is equal to the pair of its
own two fields. Chapter 8 needs that rule.

**`BinderInfo` is four values that the kernel ignores.** It records how a human
passes an argument, so a message to a human can print it. The checker never
reads it, because by the time a term reaches the kernel every argument is
already explicit.

| Value | The source writes | Who supplies the argument |
|---|---|---|
| `default` | `( )` | the caller, by hand |
| `implicit` | `{ }` | the front end, from the other arguments |
| `strictImplicit` | `⦃ ⦄` | the front end, once a later explicit argument arrives |
| `instImplicit` | `[ ]` | a search over the known instances |

### The code

Every rule in the kernel starts by asking the same question about a term: what
is at the head, and what are the arguments? The answer is called the **spine**.

```ts
function spine(e: Expr): { head: Expr; args: Expr[] } {
  const args: Expr[] = []
  while (e.k === "app") {
    args.push(e.arg)
    e = e.fun
  }
  return { head: e, args: args.reverse() }
}
```

### The rule

`app` holds exactly one argument, so `f a b` is `app(app(f, a), b)`. The tree
leans to the left, and `spine` is the undo. Hold both pictures. The tree is how
a term is stored, and the spine is how every rule reads it.

---

## 2.5 The three numbers that every node caches

### The idea

A kernel walks the same term millions of times. A question that a node can
answer out of a field costs nothing. The same question answered by a walk costs
the whole subtree, every time somebody asks.

So three numbers ride on every node. Each one is computed once, where the node
is built, out of the numbers its children already carry. Each one therefore
costs constant time per node rather than time proportional to the subtree.

### The data

```ts
interface Node {
  expr: Expr
  loose: number   // one more than the largest bvar index that points outside
  size: number    // the node count of this term as a tree
  hash: number    // the key of every cache
}
```

A bound variable index that points at a binder **inside** this node is settled.
An index that points at a binder **outside** it is **loose**, and a loose index
is the only thing substitution has to find. `loose === 0` says the node is
closed, so substitution can skip it whole.

### The code

```ts
function looseOf(e: Expr): number {
  switch (e.k) {
    case "bvar":
      return e.index + 1
    case "app":
      return Math.max(node(e.fun).loose, node(e.arg).loose)
    case "lam":
    case "forall":
      return Math.max(
        node(e.binderType).loose,
        Math.max(0, node(e.body).loose - 1),
      )
    case "let":
      return Math.max(
        node(e.binderType).loose,
        Math.max(node(e.value).loose, Math.max(0, node(e.body).loose - 1)),
      )
    case "proj":
      return node(e.value).loose
    default:
      return 0
  }
}
```

One line carries the idea. A binder subtracts one from the body, because the
body counts from inside that binder and the field counts from outside it. A
binder type does **not** subtract, because the binder is not in scope in its own
type.

What each number buys:

- **`loose`** lets substitution skip a closed subterm, and that is most of any
  real term.
- **`size`** lets the checker charge its work budget **before** a walk, in
  constant time. A walk rebuilds that many nodes, so the number is the price.
- **`hash`** is the key of the cache that remembers a reduction and the cache
  that remembers an equality.

The last one carries a rule that a reader will break at least once.

> **The hash must leave out whatever the equality test ignores.** A binder name
> is ignored, so a binder name must not enter the hash. The **shape** of a level
> is ignored as well, because two differently shaped levels can be the same
> rung, so the shape must not enter the hash either. A hash **finds** an answer.
> Equality **decides** whether to trust it.

---

## 2.6 `Declaration`

### The idea

The environment is a map from a name to a declaration. A declaration is one of
eight things.

### The data

```ts
type Hints =
  | { k: "opaque" }
  | { k: "abbrev" }
  | { k: "regular"; height: number }

type Safety = "safe" | "unsafe" | "partial"

type QuotKind = "type" | "ctor" | "lift" | "ind"

interface Base {
  name: Name
  levelParams: Name[]
  ty: Expr
}

interface RecursorRule {
  ctor: Name
  numFields: number
  rhs: Expr
}

type Declaration =
  | ({ k: "axiom"; isUnsafe: boolean } & Base)
  | ({ k: "def"; value: Expr; hints: Hints; safety: Safety; all: Name[] } & Base)
  | ({ k: "theorem"; value: Expr; all: Name[] } & Base)
  | ({ k: "opaque"; value: Expr; isUnsafe: boolean; all: Name[] } & Base)
  | ({ k: "quot"; kind: QuotKind } & Base)
  | ({ k: "inductive"; numParams: number; numIndices: number; all: Name[];
       ctors: Name[]; numNested: number; isRec: boolean;
       isReflexive: boolean; isUnsafe: boolean } & Base)
  | ({ k: "ctor"; induct: Name; cidx: number; numParams: number;
       numFields: number; isUnsafe: boolean } & Base)
  | ({ k: "recursor"; all: Name[]; numParams: number; numIndices: number;
       numMotives: number; numMinors: number; rules: RecursorRule[];
       kLike: boolean; isUnsafe: boolean } & Base)

type Environment = Map<Name, Declaration>
```

The eight cases:

- **`axiom`** is a type with no value, which is to say an assumption. The
  checker trusts it and records that it did, so a report can name every axiom a
  theorem rests on.
- **`def`** is a name with a value. The value may replace the name, and the
  name of that step is **δ**. `hints` tell the equality test which of two
  definitions to unfold first.
- **`theorem`** is a definition whose type is a proposition and whose value is a
  proof. The kernel treats the two alike. The split exists so that a tool can
  tell a proof from a program.
- **`opaque`** is a value that is checked once and then never unfolded, so the
  definition stays a black box.
- **`quot`** is a quotient type. It is built into the kernel as four fixed
  constants and one extra reduction rule.
- **`inductive`** is a data type given by its constructors. `numParams` counts
  the arguments that stay fixed across every constructor. `numIndices` counts
  the arguments that vary from one constructor to the next. The kernel treats
  the two kinds differently everywhere, so the split is not bookkeeping.
- **`ctor`** is one constructor. `cidx` is its position in the list, so a
  reduction can pick the right rule by number. `numFields` says where the fixed
  arguments end and the real data begins.
- **`recursor`** is the only primitive way to take a value apart. Each
  `RecursorRule` says what the recursor becomes for one constructor, and the
  name of that step is **ι**.

Three fields repeat across the cases, and each one is there for a reason.

- **`levelParams`** names the universe variables that this declaration is
  written against. Section 2.7 shows how a use site supplies them.
- **`all`** names every member of the mutual group. A set of definitions that
  call each other arrives as one unit and must be checked as one unit.
- **`isUnsafe`** and `safety` mark a declaration that a proof must not rest on.
  The kernel keeps checking such a declaration. It only has to make sure the
  mark travels, so a report can say what is contaminated.

**One type, and not two.** The thing that arrives to be checked and the thing
the environment stores are the same type here. That is worth stating plainly,
because the input carries more than the bare definition. A recursor arrives
**already built**, with its rules and all four of its counts. So the checker
does not derive it. It **verifies** it: one rule per constructor and no more, at
least one motive, and every rule type correct against the inductive type it
claims to eliminate. A recursor that passed no such check would be an axiom in
disguise, and an axiom in disguise proves anything.

One shape escapes that check today, and the chapter on what a checker must
check returns to it with the proof of `False` that it lets through.

### The code

```ts
function unfoldableValue(d: Declaration): Expr | null {
  if (d.k === "def" || d.k === "theorem") return d.value
  return null
}
```

Four lines, and one of them is the definition of a word. An `opaque`
declaration **holds** a value and returns `null` here. Opacity hides a value
from δ and from nothing else, so the kernel still checks that value against the
declared type.

### The rule

δ replaces a name by its value. This function says which names have one. Every
other difference between the eight cases is a difference in what gets checked,
and the first chapter of Part II holds the list.

---

## 2.7 Worked example: how a level reaches a use site

Three pieces are now on the table, so here is the one example that needs all
three.

**The declaration names its own universe variables.** A list type is stored
with `levelParams = [u]` and with this type:

```
forall(α, default, sort(succ(param u)),
                   sort(succ(param u)))
```

Read it as "given a type on rung `u`, produce a type on rung `u`". The
`param u` is a placeholder, and nothing has filled it yet.

**Each use site supplies a concrete level.** A use of the list type at rung 0 is
`const(List, [zero])`. To find the type of that term the checker does three
things.

1. Look the name up in the environment, and read its `levelParams`.
2. Check that the list of levels has the same length as `levelParams`.
   A mismatch is an error, not a default.
3. Replace `u` by `zero` everywhere in the stored type.

Step 3 gives `forall(α, default, sort 1, sort 1)`, so a list of numbers
type-checks, because a number lives on rung 1.

**A binder and a bound variable, in the same type.** The empty list has
`levelParams = [u]` and this type:

```
forall(α, implicit, sort(succ(param u)),
                    app(const(List, [param u]), bvar 0))
```

In words: for any type `α` on rung `u`, here is an empty list of `α`. Three
things from three different sections meet in that tree. The `implicit` is the
`BinderInfo` of section 2.4, and the kernel ignores it. The `param u` is the
level of section 2.3. The `bvar 0` reaches back to `α`, which is the binder
immediately above it.

**A use site can pass a variable through.** Inside a declaration whose own
`levelParams` is `[v]`, the term `const(List, [param v])` refers to that
declaration's `v`. The checker rejects any param that the enclosing declaration
did not name, and that check is the reason a param can be a bare name at all.

---

## 2.8 `LocalContext`

### The idea

To check the body of a function the checker has to go under the binder. Inside
the body, `bvar 0` refers to the argument, and the argument has a type but no
value. So the checker invents a variable, writes the type down, and puts the
invented variable into the body in place of the index.

Indices for bound variables, plus identifiers for invented ones, is called the
**locally nameless** representation. It is the standard answer, and the reason
is that each half is good at one thing. An index makes two functions that differ
only in a name into one tree. An identifier is stable under a walk, so nothing
has to be renumbered when the checker descends.

### The data

```ts
interface LocalDecl {
  id: number
  name: Name   // for the printer only
  ty: Expr
}

interface LocalContext {
  decls: LocalDecl[]
  nextId: number
}
```

A local declaration holds a type and no value. That is worth a sentence,
because a `let` plainly binds a value, and you would expect that value to land
here.

It does not. A `let` at the head of a term is reduced by putting its value
straight into its body, and the name of that step is **ζ**. So the value is
consumed where it is found, and the context never needs a field for it.

### The code

```ts
function withBinder<R>(
  ctx: LocalContext,
  name: Name,
  ty: Expr,
  f: (id: number) => R,
): R {
  const id = ctx.nextId++
  ctx.decls.push({ id, name, ty })
  try {
    return f(id)
  } finally {
    ctx.decls.pop()
  }
}
```

`nextId` only ever goes up, so an identifier is never reused inside one run,
even after the `pop`. A reused identifier would let a stale term point at the
wrong variable, and the term that results looks perfectly well formed.

### The rule

Under a binder the checker holds two things at once: a term whose indices count
from the top, and a context whose identifiers do not count at all. Chapter 3
gives the two operations that move between them.

---

## 2.9 What is left out, and why

Three things that a real term format carries do not appear above.

- **Annotations.** The format can wrap any node in data that no rule reads,
  such as a source position. Strip it where the input is read, so that no rule
  downstream has to know it exists.
- **A level hole.** `Level` can carry a hole in the same way `Expr` can. Treat
  it the same way: hold it, then refuse it.
- **Everything the front end knows.** Notation, a tactic, an instance, an
  omitted argument. A human writes a list with two brackets and two numbers
  inside. What reaches the kernel is a constructor applied to a constructor
  applied to the empty list, with the type filled in and the level chosen.
  The first chapter of Part II builds the first half of that road, and the
  chapter on the front end builds the other half.

---

## 2.10 Try it

The three numbers of section 2.5, in one file. Paste it into a TypeScript
playground.

```ts
type Expr =
  | { k: "bvar"; index: number }
  | { k: "const"; name: string }
  | { k: "app"; fun: Node; arg: Node }
  | { k: "lam"; name: string; ty: Node; body: Node }

interface Node {
  expr: Expr
  loose: number
  size: number
}

// Every node is built here, so every number is computed exactly once.
function node(expr: Expr): Node {
  return { expr, loose: looseOf(expr), size: sizeOf(expr) }
}

function looseOf(e: Expr): number {
  switch (e.k) {
    case "bvar": return e.index + 1
    case "app": return Math.max(e.fun.loose, e.arg.loose)
    case "lam": return Math.max(e.ty.loose, Math.max(0, e.body.loose - 1))
    default: return 0
  }
}

function sizeOf(e: Expr): number {
  switch (e.k) {
    case "app": return 1 + e.fun.size + e.arg.size
    case "lam": return 1 + e.ty.size + e.body.size
    default: return 1
  }
}

const nat = node({ k: "const", name: "Nat" })
const bvar = (index: number) => node({ k: "bvar", index })
const lam = (name: string, ty: Node, body: Node) =>
  node({ k: "lam", name, ty, body })

// fun x : Nat => x        closed, because the index points inside
const idNat = lam("x", nat, bvar(0))
console.log(idNat.loose, idNat.size) // 0 3

// fun x : Nat => <one further out>   not closed
const reaches = lam("x", nat, bvar(1))
console.log(reaches.loose, reaches.size) // 1 3
```

Two terms of the same size, and the numbers differ in one place. The first is
**closed**, so substitution may skip it whole, however large it is. The second
reaches outside itself, so substitution has to walk it.

Then add a hash. Compute it from the children, exactly as `looseOf` does, and
leave the binder **name** out of it. Give the same term two different binder
names and the hashes must still match, because the comparison that the kernel
uses ignores that field. Put the name in and watch the two hashes diverge. That
is the rule at the end of section 2.5, and it is one line of code away from
being broken.

---

## 2.11 Check yourself

**1. A term holds `lam(binderType: A, body: bvar 1)`. What does the index 1
refer to?**

Something outside this lambda. Index 0 would be the lambda's own argument, so
index 1 skips it and reaches one binder further out. The node is therefore not
closed, and its `loose` is 2. A term like this cannot stand alone. It only makes
sense inside at least one more binder.

**2. Why can a binder name never enter the hash of a node?**

Because the equality test ignores a binder name. Two terms that differ only in a
binder name are equal, so they must hash alike, or the cache would miss. The
rule in general: a hash may ignore more than equality does, and it may never
ignore less.

**3. The input carries a recursor with one rule, and the inductive type it names
has two constructors. What should the checker do, and why does it matter?**

Reject it. A recursor is not an assumption, so it may not be trusted. It is a
claim that follows from an inductive declaration, and a recursor with a missing
rule is a function that promises a result for a case it cannot handle. Accept it
and you can build a proof of a false statement, because the missing case never
has to be answered.

---

## 2.12 References

- de Bruijn, *Lambda calculus notation with nameless dummies*, 1972. The origin
  of the index in section 2.4.
  DOI [10.1016/1385-7258(72)90034-0](https://doi.org/10.1016/1385-7258%2872%2990034-0)
- Carneiro, *The Type Theory of Lean*, chapter 2, for the same types written as
  rules rather than as data.
  <https://github.com/digama0/lean-type-theory>
- Nederpelt and Geuvers, *Type Theory and Formal Proof*, chapter 6, for de
  Bruijn indices at book length.
  <https://www.cambridge.org/core/books/type-theory-and-formal-proof/0472640AAD34E045C7F140B46A57A67C>
- Aydemir and others, *Engineering formal metatheory*, 2008, for the locally
  nameless representation of section 2.8 and why it is the usual choice.
  DOI [10.1145/1328438.1328443](https://doi.org/10.1145/1328438.1328443)

---

**Next:** [3. Terms, binders, and names you do not need](03-terms-and-binders.md)
