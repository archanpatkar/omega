const id = `let id = (?t. \\x:t. x)`;
const pair = `let Pair = (?t1. ?t2. \\x:t1. \\y:t2. ?r. \\f:t1->t2->r. f x y)`;
const fst = `let fst = (?t1. ?t2. \\x:@R. (t1->t2->R)->R. x [t1] (\\e1:t1. \\e2:t2. e1))`;
const snd = `let snd = (?t1. ?t2. \\x:@R. (t1->t2->R)->R. x [t2] (\\e1:t1. \\e2:t2. e2))`;
const inl = `let inl = (?t1. ?t2. \\v:t1. ?r. \\b1:t1->r. \\b2:t2->r. b1 v)`;
const inr = `let inr = (?t1. ?t2. \\v:t2. ?r. \\b1:t1->r. \\b2:t2->r. b2 v)`;
const casef = `let case = (?t1. ?t2. ?j. \\v:@r.(t1->r)->(t2->r)->r. \\b1:t1->j. \\b2:t2->j. v [j] b1 b2)`;
// id,pair,fst,snd,inl,inr,casef
module.exports = [];