// Evaluater
const { Expr } = require("./ast");
const { tagged } = require("styp");
const Parser = require("./parser");
const { TypeChecker, PrimTypes } = require("./type");
const Prelude = require("./prelude");

// Eval types
const call_by_need = 0;
const call_by_name = 1;
const call_by_value = 2;

// const uops = ["NEG", "NOT"];
// const bops = ["ADD", "SUB", "DIV", "MUL", "AND", "OR", "GT", "LT", "EQ"];

class Env {
    constructor(params, args, outer = null, obj = null) {
        if (obj == null) {
            this.env = {};
            for (let i in args) {
                this.env[params[i]] = args[i];
            }
        } else {
            this.env = obj;
        }
        this.outer = outer;
    }

    find(variable) {
        if (variable in this.env) {
            return this.env[variable];
        } else if (this.outer) {
            return this.outer.find(variable);
        }
    }

    update(variable, value) {
        if (variable in this.env) {
            this.env[variable] = value;
            return this.env[variable];
        } else if (this.outer) {
            return this.outer.update(variable, value);
        }
    }

    create(variable, value) {
        return this.env[variable] = value;
    }
}

class Thunk {
    constructor(exp, env = null,intp) {
        this.exp = exp;
        this.scope = env;
        this.reduced = false;
        this.intp = intp;
    }

    value() {
        return this.intp.ieval(this.exp, this.scope);
    }

    reduce() {
        if(!this.reduced)
        {
            this.exp = this.intp.ieval(this.exp, this.scope);
            this.reduced = true;
        }
        return this.exp;
    }

    toString() {
        return `<thunk>`;   
    }
}

class Lambda {
    constructor(body, param, env = null, intp) {
        this.body = body;
        this.param = param;
        this.scope = env;
        this.intp = intp;
    }

    apply(actual) {
        let frame = new Env(null, null, this.scope, {});
        frame.create(this.param, actual);
        const out = this.intp.ieval(this.body, frame);
        return out;
    }

    toString() {
        return this.scope && this.scope != GLOBAL?"<closure>":"<lambda>";   
    }
}

const pair = tagged("Pair",["fst","snd"]);

pair.prototype.apply = function(f) { 
    return f.apply(this.fst).apply(this.snd);
}

pair.prototype.toString = function() {
    return `(${this.fst},${this.snd})`;
}

// WIP
// const print = {
//     apply(f) {
//         console.log(f);
//         return PrimTypes.unit
//     }
// };

const opfuns = {
    "ADD": (a,b) => a + b,
    "MUL": (a,b) => a * b,
    "SUB": (a,b) => a - b,
    "DIV": (a,b) => a / b,
    "AND": (a,b) => a && b,
    "OR": (a,b) => a || b,
    "GT": (a,b) => a > b,
    "LT": (a,b) => a < b,
    "EQ": (a,b) => a === b,
    "NOT": a => !a,
    "NEG": a => -a
};

function globalEnv() {
    const env = new Env();
    // Will add more
    // env.create("fst",{ apply: v => v[0] });
    // env.create("snd",{ apply: v => v[1] });
    // env.create("print",{ apply: v => console.log(v) });
    return env;
}

const GLOBAL = globalEnv();

class Interpreter { 
    constructor(global) {
        this.parser = new Parser();
        this.checker = new TypeChecker();
        this.mode = call_by_value;
        this.global = global?global:GLOBAL;
        console.log("--:: Prelude ::--");
        Prelude.forEach(f => {
            console.log(f);
            this.evaluate(f);
        });
    }

    setMode(mode) {
        this.mode = mode;
    }

    ieval(ast, env) {
        return ast.cata({
            TCons: t => t.toString(),
            TCApp: t => t.toString(),
            TLam: t => this.ieval(t.body,env),
            TApp: ta => this.ieval(ta.tl,env),
            Lit: ({ val }) => val,
            Pair: ({ fst, snd }) => pair(
                this.ieval(fst,env),
                this.ieval(snd,env),
            ),
            Let: ({ name, e1, e2 }) => {
                if(this.mode == call_by_value)
                    e1 = this.ieval(e1,env);
                else e1 = new Thunk(e1,env,this);
                if(e2) {
                    let ls = new Env(null, null, env, {});
                    ls.create(name, e1);
                    return this.ieval(e2,ls);
                }
                return env.create(name,e1);
            },
            Var: ({ name }) => {
                const v = env.find(name);
                if (v instanceof Thunk) {
                    if(this.mode == call_by_name) return v.value();
                    return v.reduce();
                }
                return v;
            },
            Cond: ({ cond, e1, e2 }) => this.ieval(cond, env) ? 
                                        this.ieval(e1, env): 
                                        this.ieval(e2, env),
            Lam: ({ param, body }) => new Lambda(body, param, env, this),
            App: ({ e1, e2 }) => {
                const lam = this.ieval(e1,env);
                return this.mode == call_by_value ? 
                    lam.apply(this.ieval(e2,env)):
                    lam.apply(new Thunk(e2,env,this));
            },
            Fix: ({ e }) => this.ieval(e.body,env),
            BinOp: ({ op, l, r }) => opfuns[op](this.ieval(l, env),this.ieval(r, env)),
            UnOp: ({ op, v }) => opfuns[op](this.ieval(v,env))
        });
    }

    evaluate(str) {
        const ast = this.parser.parse(str);
        console.log("AST:");
        console.log(ast.toString());
        const type = this.checker.prove(ast);
        console.log("Type:");
        console.log(type);
        // let output = this.ieval(ast,this.global);
        // if(Expr.is(output)) output = `<Tlambda>`
        return { output:"", type:"" };
    }
}

module.exports =  {
    Interpreter:Interpreter, 
    modes: {
        "need":call_by_need,
        "name":call_by_name,
        "value":call_by_value
    }
};