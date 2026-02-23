# connesLean
Christopher Long's proof of Restricted Weil Quadratic Form, formalized in Lean

The original proof is at https://github.com/octonion/mathematics/tree/main/connes and the version I am using is in lamportportform.tex

The outline of the formalization is in outline.md 

Each of the stages will be tracked with GitHub issues. I use GitHub Codespaces for a dev environment, setup with bootstrap.sh

The workflow I use is:

For each issue, I will ask Claude to plan one or more steps to formalize the proof. The plan will be reviewed by me, and I will ask Claude to look for corner cases that may have been missed.

Once the plan is accepted, I will have Clade commit it as a document to docs/ and begin work in a new branch. When the work is complete, the branch will be committed and a PR opened. I will ask for a review by Copilot of the work on the branch, and all comments will be resolved before continuing on any other work. 

I will ask for LSpec property tests of all definitions, axioms and theorems. https://github.com/argumentcomputer/LSpec 

The first pass of the proof may contain axioms, and sorrys, both of which allow the delay of more difficult sections until the full skeleton of the proof is done. Then there will be a second pass to remove axioms and replace them with theorems. A third pass to remove sorrys. A fourth path to examine definitions carefully. Each will get the proof closer to good quality.

I'm not that familiar with analysis or measure theory, so this may not go well at all. Or it might go quite well.

![HB1WYU7akAAe7sU](https://github.com/user-attachments/assets/e5844547-f516-4f81-b0c1-75a501fa5559)
