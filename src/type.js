// Type checker
// Based on -
// https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture30.pdf
// https://www.cl.cam.ac.uk/teaching/1415/L28/lambda.pdf
// https://crypto.stanford.edu/~blynn/lambda/typo.html

// TODO: Improve and optimize
// TODO: the current implementation of the kinding system is a !very! adhoc will restructure the whole thing,
// also cover all the kind check cases and seperate and clean up access of all the contexts
// Dep
const { equal } = require("saman");
const { sum, tagged } = require("styp");
const { Expr } = require("./ast");
const Parser = require("./parser");

// Renamed vars prefix
let gcount = 0;
const globalPrefix = _ => `_tlam_v_${gcount++}`;

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"],
    Forall: ["var", "kind", "type"],
    Hole: ["type"]
});

const Kind = sum("Kind", {
    Star:["type"],
    KArr:["k1","k2"]
});

const TClosure = tagged("TClosure",["env","to"]);
const Hole = Symbol("Hole");
const TNumber = Type.TCon("number");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const PrimTypes = {
    "number":TNumber,
    "bool":TBool,
    "unit":TUnit
};

const optypes = {
    "ADD": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "MUL": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "SUB": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "DIV": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "AND": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "OR": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "GT": Type.TArr(TNumber,Type.TArr(TNumber,TBool)),
    "LT": Type.TArr(TNumber,Type.TArr(TNumber,TBool)),
    "NOT": Type.TArr(TBool,TBool),
    "NEG": Type.TArr(TNumber,TNumber),
    "EQ": Type.Forall(
        [Type.TVar("o1")], Kind.Star("*"),
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o1"),TBool))
    )
}

function convertType(type) {
    if(Type.is(type)) return type;
    if(type === "number") return TNumber;
    if(type === "bool") return TBool;
    if(type === "unit") return TUnit;
    if(typeof type === "string") return Type.TVar(type);
    if(Expr.Var.is(type)) return Type.TVar(type.name);
    if(Array.isArray(type)) return Type.TArr(convertType(type[0]),convertType(type[1]));
    if(typeof type === "object") return Type.Forall([Type.TVar(type.var)],convertKind(type.kind),convertType(type.type));
}

function convertKind(kind) {
    if(Kind.is(kind)) return kind;
    if(kind === "*" || Type.is(kind)) return Kind.Star("*");
    if(Array.isArray(kind)) return Kind.KArr(convertKind(kind[0]),convertKind(kind[1]));
}

function printType(type,level=0) {
    if(Kind.is(type)) {
        return type.cata({
            Star: _ => _.type,
            KArr: ({k1, k2}) => `${printType(k1)} => ${printType(k2)}`
        });
    }
    if(Expr.TCApp.is(type)) {
        return `(${printType(type.to1)} ${printType(type.to2)})`
    }
    return type.cata({
        TCon: ({ name }) => name,
        TVar: ({ v }) => v,
        TArr: ({ t1, t2 }) => `${level?"(":""}${printType(t1,level+1)} -> ${printType(t2,level+1)}${level?")":""}`,
        Forall: f => f.var.length?`∀ ${f.var.map(e => printType(e,level+1)).join(" ")}::${printType(f.kind)}. ${printType(f.type,level+1)}`: printType(f.type,level+1),
        Hole: h => printType(h.type)
    });
}

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable: '${name}'`);
const notAType = (type) => genericError(`Expected a type`);
const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);
const nonGenFunction = (type) => genericError(`Not ${printType(type)} a Generic / Type Lambda`);

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if (this.parent) return this.parent.exists(name);
        return false;
    }

    addBinding(name, type) {
        if(name in this.env) defInScope(name);
        this.env[name] = type;
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {  
        if (this.env[name]) return this.env[name];
        if (this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.env = new TypeEnv(null);
        this.tenv = new TypeEnv(null);
        this.varInit();
    }

    varInit() {
        this.names = {};
        this.count = 0;
        for(let i = "a".charCodeAt(0);i < "z".charCodeAt(0);i++) {
            this.names[i-97] = [String.fromCharCode(i),0];
        }
    }

    fresh(prefix="") {
        const pair = this.names[this.count++ % 25];
        let n = pair[1]++;
        return Type.TVar(`${prefix}${pair[0]}${n?n:""}`);
    }

    rename(type,map) {
        return type.cata({
            TCon: t => t,
            TVar: ({ v }) => v in map? map[v]:Type.TVar(v),
            TArr: ({ t1, t2 }) => Type.TArr(this.rename(t1,map), this.rename(t2,map)),
            Forall: f => Type.Forall(f.var,f.kind,this.rename(f.type,map)),
            Hole: h => h
        });
    }

    verifyType(type) {
        return Type.is(type);
    }

    equalTypes(t1,t2) {
        if(Type.Forall.is(t1) && Type.Forall.is(t2)) {
            const tv = this.fresh();
            const map = {}
            map[t1.var[0].v] = tv;
            map[t2.var[0].v] = tv;
            const mt1 = this.rename(t1.type,map);
            const mt2 = this.rename(t2.type,map);
            return this.equalTypes(mt1,mt2);
        }
        return equal(t1,t2);
    }

    subsR(type,map) {
        return type.cata({
            TCon: t => t,
            TVar: ({ v }) => map.exists(v)? map.lookUp(v):Type.TVar(v),
            TArr: ({ t1, t2 }) => Type.TArr(this.subsR(t1,map), this.subsR(t2,map)),
            Forall: f => Type.Forall(f.var,f.kind,this.subsR(f.type,map)),
            Hole: h => h
        });
    }

    subst(ast,map) {
        if(TClosure.is(ast)) {
            if(map.exists(ast.var)) {
                let temp = {}
                let name = globalPrefix();
                temp[ast.var] = Expr.Var(name)
                return Expr.TCons(name,ast.kind,this.subst(ast.body, temp));
            }
            return ast;
        } 
        if(Expr.TCApp.is(ast)) {
            return Expr.TCApp(
                this.subst(ast.to1,map),
                this.subst(ast.to2,map)
            );
        }
        return this.subsR(convertType(ast),map);
    }

    createClosure(type,env,tenv) {
        if(Expr.Var.is(type)) {
            let v = tenv.exists(type.name);
            if(Expr.is(v) || !Kind.is(v)) return v;
            v = env.exists(type.name);
            if(Expr.is(v) || Kind.is(v)) return this.createClosure(v,env,tenv);
            return convertType(type);
        }
        if(TClosure.is(type) && (Expr.TCons.is(type.to) || Expr.TCApp.is(type.to))) {
            return this.createClosure(type.to,env,type.env);
        }
        if(Expr.TCons.is(type)) {
            let fenv = new TypeEnv(tenv);
            fenv.addBinding(type.var.name,convertKind(type.kind));
            let func = TClosure(fenv,Expr.TCons(type.var,type.kind,this.createClosure(type.body,env,fenv)));
            return func;
        }
        if(Expr.TCApp.is(type)) {
            this.check(type,env,tenv);
            return type;
        }
        return convertType(type);
    }

    handleTypes(type,env,tenv=this.tenv,flag=true) {
        if(Type.is(type)) return type;
        if(Expr.TCApp.is(type)) {
            if(flag) this.check(type,env,tenv);
            const to1 = TClosure.is(type.to1) ? type.to1:this.handleTypes(type.to1,env,tenv,flag);
            const to2 = TClosure.is(type.to1) ? type.to2:this.handleTypes(type.to2,env,tenv,flag);
            if(to1 === Hole) return Type.Hole(convertType(type));
            if(!TClosure.is(to1)) genericError("Requires a Type Operator");
            to1.env.removeBinding(to1.to.var.name);
            to1.env.addBinding(to1.to.var.name,to2);
            let out = this.subst(to1.to.body,to1.env);
            if(!Type.is(out) && flag) out = this.handleTypes(out,env,tenv,false);
            return out
        }
        return this.createClosure(type,env,tenv);
    }

    checkCond(ast,env,tenv) {
        const cond = this.check(ast.cond, env);
        const t1 = this.check(ast.e1, env);
        const t2 = this.check(ast.e2, env);
        if(!this.equalTypes(cond,TBool)) typeMismatch(TBool,cond);
        if(!this.equalTypes(t1,t2)) typeMismatch(t1,t2);
        return t1;
    }

    checkLet(ast,env,tenv) {
        let t1;
        if(Expr.TCons.is(ast.e1)) t1 = ast.e1; 
        else if(Expr.TCApp.is(ast.e1)) t1 = this.handleTypes(ast.e1,env,tenv);
        else t1 = this.check(ast.e1,env);
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, t1);
            return this.check(ast.e2,ne);
        }
        env.addBinding(ast.name,t1);
        return Type.is(t1) || Kind.is(t1)? t1 : this.check(ast.e1);
    }

    checkTLam(ast,env,tenv) {
        let tk = convertKind(ast.kind);
        if(Kind.KArr.is(tk) && !tenv.exists(ast.param)) {
            return Type.Hole(Type.TArr(tk,Kind.Star("⊥")));
        }
        const tv = convertType(ast.param);
        this.tenv.addBinding(tv.v, tk);
        if(!this.verifyType(tv)) notAType(tv);
        const body = this.check(ast.body, env, tenv);
        this.tenv.removeBinding(tv.v);
        const out = Type.Forall([tv],tk,body);
        return out;
    }

    checkLam(ast,env,tenv) {
        let vt = this.handleTypes(ast.type,env,tenv);
        if(vt === Hole) vt = ast.type;
        else if(!this.verifyType(vt)) notAType(vt);
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, vt);
        const body = this.check(ast.body, ne);
        return Type.TArr(vt, body);
    }

    checkApp(ast,env,tenv) {
        const t1 = this.check(ast.e1, env);
        const t2 = this.check(ast.e2, env);
        if(!Type.TArr.is(t1)) nonFunction(t1);
        if(!this.equalTypes(t1.t1,t2)) typeMismatch(t1.t1,t2);
        return t1.t2;
    }
    
    checkTempTL(ast,t1,t2,env,tenv) {
        const tk = convertKind(ast.tl.kind);
        if(!equal(tk,t2) && !TClosure.is(t2)) genericError("Not matching kinds");
        const tv = convertType(ast.tl.param);
        const local = new TypeEnv(tenv);
        local.addBinding(ast.tl.param,t2);
        const body = this.check(ast.tl.body, env, local);
        const out = Type.Forall([tv],tk,body);
        return out;
    }

    checkTApp(ast,env,tenv) {
        const t1 = this.check(ast.tl, env);
        const t2 = this.handleTypes(ast.t,env,tenv);
        if(!this.verifyType(t2) && !t1 === Hole) notAType(t2);
        if(!Type.Forall.is(t1) && !t1 === Hole) nonGenFunction(t1);
        let kt;
        if(Expr.TCons.is(ast.t) || Expr.TCApp.is(ast.t)) kt = this.check(ast.t,env,tenv);
        else kt = convertKind("*");
        if(!Kind.KArr.is(kt) && !this.verifyType(t2) && !t1 === Hole) notAType(t2);
        if(!equal(t1.kind,kt) && !t1 === Hole) genericError("Kinds do not match!");
        if(Type.Hole.is(t1)) {
            return this.checkTempTL(ast,t1,t2,env,tenv);
        }
        const map = {}
        map[t1.var[0].v] = t2;
        return this.rename(t1.type,map);
    }

    checkTCons(ast,env,tenv) {
        const vt = convertKind(ast.kind);
        const ne = new TypeEnv(tenv);
        ne.addBinding(ast.var.name, vt);
        let body;
        if(Expr.is(ast.body)) body = this.checkHKT(ast.body,env,ne);
        else body = convertType(ast.body);
        if(Type.is(body)) body = convertKind("*");
        return Kind.KArr(vt, body);
    }

    checkTCApp(ast,env,tenv) {
        const t1 = this.checkHKT(ast.to1, env, tenv);
        let t2;
        if(Expr.is(ast.to2)) t2 = convertKind(this.checkHKT(ast.to2, env, tenv));
        else t2 = convertKind(convertType(ast.to2));
        if(!Kind.KArr.is(t1) && !t1 === Hole) nonFunction(t1);
        if((!TClosure.is(t1) || !equal(t1.k1,t2)) && !t1 === Hole) typeMismatch(t1.k1,t2);
        return TClosure.is(t1)?t1:t1.k2;
    }

    checkUnOp(ast,env,tenv) {
        const t = this.check(ast.v,env,tenv);
        const op = optypes[ast.op];
        if(!this.equalTypes(op.t1,t)) typeMismatch(op.t1,t);
        return op.t2;
    }
    
    checkBinOp(ast,env,tenv) {
        const t1 = this.check(ast.l,env,tenv);
        const t2 = this.check(ast.r,env,tenv);
        let op = optypes[ast.op];
        if(Type.Forall.is(op)) {   
            const map = {}
            map[op.var[0].v] = t1;
            op = this.rename(op.type,map);
        }
        if(Type.is(op)) {
            if(!this.equalTypes(op.t1,t1)) typeMismatch(op.t1,t1);
            if(!this.equalTypes(op.t2.t1,t2)) typeMismatch(op.t2.t1,t2);
            return op.t2.t2;
        }
        return TUnit;
    }

    checkHKT(ast,env,tenv) {
        if(Expr.Var.is(ast) && tenv.exists(ast.name)) return tenv.lookUp(ast.name);
        return this.check(ast,env,tenv);
    }

    check(ast, env = this.env, tenv = this.tenv) {
        return ast.cata({
            Lit: ({ type }) => PrimTypes[type],
            Var: ({ name }) => {
                const e = env.lookUp(name);
                if(Expr.is(e)) return this.check(e,env,tenv)
                return e;
            },
            UnOp: u => this.checkUnOp(u,env,tenv),
            BinOp: b => this.checkBinOp(b,env,tenv),
            Cond: c => this.checkCond(c,env,tenv),
            Lam: l => this.checkLam(l,env,tenv),
            App: a => this.checkApp(a,env,tenv),
            TApp: a => this.checkTApp(a,env,tenv),
            TLam: t => this.checkTLam(t,env,tenv),
            TCons: cn => this.checkTCons(cn,env,tenv),
            TCApp: tc => this.checkTCApp(tc,env,tenv),
            Let: lb => this.checkLet(lb,env,tenv)
        });
    }

    prove(ast) {
        return printType(this.check(ast));
    }
}

// \x:((\t1::*=>*=>*. t1 number number) TPair). x
// const p1 = new Parser();
// const tc1 = new TypeChecker();
// console.log(tc1.prove(p1.parse("(\\x:((\\t::*=>*. t number) (\\x::*. x)). x)")))
// console.log(tc1.prove(p1.parse("\\x:((\\x::*=>*=>*. x number number) (\\t1::*. \\t2::*. @R. (t1->t2->R)->R)). x")))
// console.log(tc1.prove(p1.parse("(?a::*=>*. \\n:(a bool). n) [\\x::*. x]")))
// console.log(tc1.prove(p1.parse("(?a::*=>*=>*. \\n:(a number bool). n) [\\x::*. \\y::*. y]")))
module.exports = { TypeChecker, PrimTypes, printType }; 