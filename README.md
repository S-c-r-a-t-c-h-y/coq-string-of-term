# coq-string-of-term

A Coq plugin that provides a way to convert Coq terms into their string representation.

## Installation

To install this plugin, open a terminal and run the following commands :

```bash
git clone https://github.com/S-c-r-a-t-c-h-y/coq-string-of-term
cd coq-string-of-term
opam install --working-dir
```

This requires having `opam` installed.

To use the plugin in your scripts after installing it, import it using `Load StringOfTerm`.

## Functionalities

This plugin implements two kinds of tactics.

### Retrieving the Coq string

- `pose_string_of_term name term` poses a new hypotheses in the context named `name` and whose definition is the Coq string representing the term `term` (as is printed by `idtac term`)
- `pose_string_of_intropattern name intropattern` poses a new hypotheses in the context named `name` and whose definition is the Coq string representing the intropattern `intropattern` (as is printed by `idtac intropattern`)

### Printing the Coq string

- `print_string_of_term term` prints the Coq string representing the term `term` (as is printed by `idtac term`)
- `print_string_of_intropattern intropattern` prints the Coq string representing the intropattern `intropattern` (as is printed by `idtac intropattern`)

## Examples

Executing

```coq
Goal forall (f : R -> R) (x : R), ex_derive f x -> continuity_pt f x.
Proof.
match goal with
| |- ?g => pose_string_of_term goal_str g
end.
```

adds the hypotheses `goal_str := "forall (f : R -> R) (x : R), ex_derive f x -> continuity_pt f x" : string` to the context.

Then executing

```coq
match goal with
| |- forall (binder : _), _ => pose_string_of_intropattern binder_str binder
end.
```

adds the hypotheses `binder_str := "f" : string` to the context.
