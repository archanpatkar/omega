// Type checker
// Based on -
// https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture22.pdf
// https://www.cl.cam.ac.uk/teaching/1415/L28/lambda.pdf
// https://crypto.stanford.edu/~blynn/lambda/systemf.html

// TODO: Improve and optimize
// the code is in a bit of a mess will restructure the whole thing
// Dep
const { equal } = require("saman");
const { sum, tagged } = require("styp");
const { Expr } = require("./ast");

// Renamed vars prefix
let gcount = 0;
const globalPrefix = _ => `_tlam_v_${gcount++}`;

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"],
    Forall: ["var", "type"]
});

const Kind = sum("Kind", {
    Star:["type"],
    KArr:["k1","k2"]
});

const TClosure = tagged("TClosure",["env","to"]);

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
        [Type.TVar("o1")],
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o1"),TBool))
    )
}

function convertType(type) {
    if(Type.is(type)) return type;
    if(type === "number") return TNumber;
    if(type === "bool") return TBool;
    if(type === "unit") return TUnit;
    if(typeof type === "string" || Expr.Var.is(type)) return Type.TVar(type);
    if(Array.isArray(type)) return Type.TArr(convertType(type[0]),convertType(type[1]));
    if(typeof type === "object") return Type.Forall([Type.TVar(type.var)],convertType(type.type));
}

function convertKind(kind) {
    if(kind === "*" || Type.is(kind)) return Kind.Star("*");
    if(Array.isArray(kind)) return Kind.KArr(convertKind(kind[0]),convertKind(kind[1]));
}

function printType(type,level=0) {
    if(Kind.is(type)) {
        return type.cata({
            Star: _ => "*",
            KArr: ({k1, k2}) => `${printType(k1)} => ${printType(k2)}`
        });
    }
    return type.cata({
        TCon: ({ name }) => name,
        TVar: ({ v }) => v,
        TArr: ({ t1, t2 }) => `${level?"(":""}${printType(t1,level+1)} -> ${printType(t2,level+1)}${level?")":""}`,
        Forall: f => f.var.length?`forall ${f.var.map(e => printType(e,level+1)).join(" ")}. ${printType(f.type,level+1)}`: printType(f.type,level+1)
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
        else if (this.parent) return this.parent.lookUp(name);
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
        // console.log("inside rename")
        // console.log(type?type.toString():"undef");
        return type.cata({
            TCon: t => t,
            TVar: ({ v }) => v in map? map[v]:Type.TVar(v),
            TArr: ({ t1, t2 }) => Type.TArr(this.rename(t1,map), this.rename(t2,map)),
            Forall: f => Type.Forall(f.var,this.rename(f.type,map))
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

    // currently ignores variable shadowing!
    // \x:int. \x:bool. x
    subst(ast,map={}) {
        // console.log("Substitution starts here -->");
        // console.log(ast.toString());
        // console.log(map)
        if(TClosure.is(ast)) {
            if(ast.var in map) {
                let temp = {}
                let name = globalPrefix();
                temp[ast.var] = Type.TVar(name)
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
        const ct = convertType(ast);
        // console.log("converted")
        // console.log(ct)
        return this.rename(ct,map);
    }


    handleTypes(type,tenv=this.tenv.env) {
        // console.log("Handle types starts here -->");
        // console.log(type);
        console.log("Current Type Environment")
        console.log(tenv)
        if(Expr.Var.is(type) && ) return this.handleTypes(tenv[type.name],tenv);
        if(Expr.TCons.is(type)) {
            let env = {__proto__:tenv};
            let func = TClosure(env,Expr.TCons(type.var,type.kind,this.handleTypes(type.body,env)));
            // console.log("closure function");
            // console.log(func);
            return func;
        }
            // const t = this.check(type);
        if(Expr.TCApp.is(type)) {
            const t = this.check(type);
            console.log("ast to1")
            console.log(type.to1)
            const to1 = this.handleTypes(type.to1,tenv);
            // console.log(`hto1: ${to1}`)
            const to2 = this.handleTypes(type.to2,tenv);
            // console.log(`hto2: ${to2}`)
            // if(Expr.Var.is(to1)) to1 = tenv[to1.name]; // later
            // Expr.TCons.is(to1)
            console.log("TO1|---->")
            console.log(to1)
            if(TClosure.is(to1)) {
                // const map = { __proto__:to1.env }
                to1.env[to1.to.var] = to2
                const out = this.subst(to1.to.body,to1.env);
                // console.log("out type:")
                // console.log(out);
                return out
            }
            else genericError("Requires a Type Operator");
        }
        return convertType(type);
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
        if(Expr.TCons.is(ast) || Expr.TCApp.is(ast)) t1 = ast.e1;
        else t1 = this.check(ast.e1,env);
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, t1);
            return this.check(ast.e2,ne);
        }
        env.addBinding(ast.name,t1);
        return t1;
    }

    checkTLam(ast,env,tenv) {
        const tv = this.handleTypes(ast.param);
        if(!this.verifyType(tv)) notAType(tv);
        this.tenv.addBinding(tv.v, convertKind(ast.kind));
        const body = this.check(ast.body, env);
        this.tenv.removeBinding(tv.v);
        return Type.Forall([tv],body);
    }

    checkLam(ast,env,tenv) {
        const vt = this.handleTypes(ast.type);
        if(!this.verifyType(vt)) notAType(vt);
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

    checkTApp(ast,env,tenv) {
        const t1 = this.check(ast.tl, env);
        const t2 = this.handleTypes(ast.t);
        if(!this.verifyType(t2)) notAType(t2);
        if(!Type.Forall.is(t1)) nonGenFunction(t1);
        const map = {}
        map[t1.var[0].v] = t2;
        return this.rename(t1.type,map);
    }

    checkTCons(ast,env,tenv) {
        const vt = convertKind(ast.kind);
        const ne = new TypeEnv(tenv);
        ne.addBinding(ast.param, vt);
        let body;
        if(Expr.is(ast.body)) body = this.checkHKT(ast.body,env,ne);
        else body = convertType(ast.body);
        if(Type.is(body)) body = convertKind("*");
        return Kind.KArr(vt, body);
    }

    checkTCApp(ast,env,tenv) {
        // console.log("Inside TCApp");
        const t1 = this.checkHKT(ast.to1, env, tenv);
        let t2;
        if(Expr.is(ast.to2)) t2 = this.checkHKT(ast.to2, env, tenv);
        else t2 = convertKind(convertType(ast.to2));
        if(!Kind.KArr.is(t1)) nonFunction(t1);
        // console.log("type1");
        // console.log(t1.toString());
        // console.log("type2");
        // console.log(t2.toString());
        if(!equal(t1.k1,t2)) typeMismatch(t1.k1,t2);
        return t1.k2;
    }

    checkUnOp(ast,env,tenv) {
        const t = this.check(ast.v,env,tenv);
        const op = optypes[ast.op];
        if(!this.equalTypes(op.t1,t)) typeMismatch(op.t1,t);
        return op.t2;
    }
    
    checkBinOp(ast,env,tenv) {
        const t1 = this.check(ast.l,env);
        const t2 = this.check(ast.r,env);
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
        console.log("check--")
        console.log(ast.toString());
        if(Kind.is(ast)) return ast;
        if(Type.is(ast)) return ast;
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

// const tc1 = new TypeChecker();

// const ex1 = Expr.Lam("y",Expr.TCApp(Expr.TCons("x","*","x"),"number"),Expr.Var("y"));
// const ex2 = Expr.Lam("y",Expr.TCApp(Expr.TCApp(Expr.TCons("x","*",Expr.TCons("z","*","x")),"bool"),"bool"),Expr.Var("y"));
// const ex3 = Expr.Lam("y",Expr.TCApp(Expr.TCApp(Expr.TCons("x","*",Expr.TCons("z","*",{var:"r",kind:"*",type:["x",["z","r"]]})),"number"),"bool"),Expr.TApp(Expr.Var("y"),"number"));
// const ex4 = Expr.Lam("y",Expr.TCApp(Expr.TCApp(Expr.TCons("x","*",Expr.TCons("x","*","x")),"bool"),"number"),Expr.Var("y"));
// console.log(printType(tc1.check(ex1)));
// console.log(printType(tc1.check(ex2)));
// console.log(printType(tc1.check(ex3)));
// console.log(printType(tc1.check(ex4)));

// test examples

// let Pair = \x::*. \y::*. @r. (x -> y -> r) -> r
// let fst = (?t1. ?t2. \x:(Pair t1 t2). x [t1] (\e1:t1. \e2:t2. e1))
// let snd = (?t1. ?t2. \x:(Pair t1 t2). x [t2] (\e1:t1. \e2:t2. e2))

// \x::*. \y::*. x -> y
// \x::*. \y::*. x
// \x::*. \y::*. x y
// \x::*. \y::*. @r. x -> y -> r
module.exports = { TypeChecker, PrimTypes };