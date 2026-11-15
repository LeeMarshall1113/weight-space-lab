# Component rubric (PREREG_XF A3). Fixed before any judging.

You compare a SUBMITTED RASP program with the TRUE program. You do not know which method
produced the submission. Judge only what the code computes, not its comments. Comments are
stripped anyway.

Score each component **1** (the same as the true program), **0.5** (partly right, e.g. most
table entries right, or the right kind of operation with a wrong detail) or **0** (wrong or
absent). Use **"NA"** if the component does not exist in the true program.

## C1: value table
Compare the mapping from tokens, or from counts, to output values.

- **Token tables:** compare entry by entry. Score 1 if every token maps right, 0.5 if most
  do, 0 otherwise.
- **Count-based outputs:** compare the modulus or the threshold.
- **Permute templates:** the `val` table.

## C2: routing
Compare which positions feed each output position:
- the position itself;
- the next position (i+1);
- the previous position (i-1);
- the mirror position (n-1-i);
- all positions, through a count or an aggregate.

## C3: comparison
Compare the Select (or Selects): what is compared (tokens, indices, or a Map of tokens
into groups), and with which comparison operator. Any token grouping counts here: score 1
only if the groups match.

## C4: combination
Compare how the parts become the output:
- a mod m of a count;
- a threshold on a count;
- (count + g(token)) mod m;
- an Aggregate default value at the boundary.

## Output
Output one JSON line per pair:

    {"pair": <id>, "C1": x, "C2": x, "C3": x, "C4": x}
