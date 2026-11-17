# CeTTa crash on long MeTTa-backend searches

`cetta 1.5.0-dev (core)`, `--lang petta@1.0.6`.

A long run of the prover on the MeTTa backend ends in

```
Fatal memory fault (SIGSEGV); stack overflow is one possible cause.
```

after about 95 s and about 4,700 search steps, always near the same point.

## Not a stack overflow

- `ulimit -s unlimited`, `--num-threads 1` and `--eval-hashcons` all crash the
  same way.
- The backtrace at the fault is 18 frames deep:

```
#0  oem_trace_atom ()
#1  oem_collect_generation ()
#2  oem_cursor_run_plain ()
#3  cetta_open_equation_cursor_continue ()
#4  petta_machine_open_resume ()
#5  petta_machine_dispatch_goal.constprop ()
#6  petta_machine_next ()
#7  petta_eval_machine_run.isra ()
#8  petta_eval_machine_try ()
#9  metta_call_impl ()
...
#15 cetta_main ()
```

- Peak resident memory at the crash is 685 MB on a 15 GB machine.
- Printing a little more during the run moves the crash to an earlier state,
  so it depends on how much has been allocated, not on one term.

The fault is in the runtime's generation collection (`oem_collect_generation`
-> `oem_trace_atom`), which suggests a dangling atom reference when a
generation is collected after many atoms have been added to and removed from
`&self`.

## To reproduce

```bash
cd phase2/cetta
cetta --lang petta@1.0.6 prove.metta quotient_remainder_int /tmp/out.jsonl 40 5000 900 "" metta
```

Shorter runs (3,000 steps, e.g. case 1 with or without hints) finish normally.
The same search on the Lean backend (`... lean`) also runs 5,000 steps without
a crash; the MeTTa backend additionally keeps one `(MSt n goals)` atom per
proof state in `&self`.

## Second reproduction (2026-11-17): crash moves when printing is added

Case 1 with the 30 hints chosen by `../hints.metta`
(`prove.metta quotient_remainder_int_nat out.jsonl 40 <budget> 600 auto metta`,
after the change that records applied lemmas per state):

| budget | result |
|---|---|
| 300, 302 ... 313 | finishes normally |
| 314, 315, 316, 320 ... 3000 | SIGSEGV at the same point, about 23 s in |

`ulimit -s unlimited`, `CETTA_GC=0`, `CETTA_GC=off` and
`CETTA_GC_BUDGET_MB=8000` crash the same way. Adding one `println!` per step
(in `p2:metta-try`) makes the same 600-step run finish normally: the fault
depends on the allocation pattern, not on one step or term, as before.
