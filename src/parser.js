// TDOP/Pratt Parser
// Based on http://crockford.com/javascript/tdop/tdop.html
const tokenize = require("./lexer");
const { Expr } = require("./ast");

const ops = ["ADD", "SUB", "DIV", "MUL", "LBR", "AND", "OR", "GT", "LT", "EQ", "NEG", "NOT"];
const not = ["EOF", "DEFT", "DEFK", "DOT", "RBR", "RPAREN", "BODY", "IN", "THEN", "ELSE", "COMMA"];

// Prec table
// or - 1
// and - 2
// eq - 3
// gt - 4
// lt - 4
// add - 5
// sub - 5
// mul - 6
// div - 6
// neg - 7
// not - 7
// Type apply - 8
// apply - 9
const handlers = {
    "COMMA": {
        nud() {
            this.expect(null,"',' is not a unary operator");
        }
    },
    "IN": {
        nud() {
            this.expect(null,"'in' is not a unary operator");
        }
    },
    "DOT": {
        nud() {
            this.expect(null,"'.' is not a unary operator");
        } 
    },
    "TO": {
        nud() {
            this.expect(null,"'->' is not a unary operator");
        } 
    },
    "FORALL": {
        nud() {
            this.expect(null,"'@' is not a unary operator");
        } 
    },
    "IDEN": {
        nud(token) {
            return Expr.Var(token.value);
        },
        led(left) {
            this.expect(null,`'${left.name}' not a binary operator`);
        }
    },
    "LIT": {
        nud(token) {
            if (typeof token.value == "number") return Expr.Lit("number", token.value);
            return Expr.Lit("bool", token.value);
        },
        led(left) {
            this.expect(null,`'${left.val}' not a binary operator`);
        }
    },
    "LPAREN": {
        nud() {
            const exp = this.expression(0);
            this.expect("RPAREN", "Unmatched paren '('");
            if(!exp) return Expr.Lit("unit","unit");
            return exp;
        },
        led() {
            this.expect(null,"'(' not a binary operator");
        }
    },
    "LET": {
        nud() {
            const name = this.expect("IDEN","Expected an identifier").value;
            // let vars;
            // let nt = this.peek();
            // let nt = this.peek();
            // if(nt && nt.type == "IDEN") {
            //     vars = [this.consume().value];
            //     while((nt=this.peek()) && nt.type == "IDEN")
            //         vars.push(this.consume().value);
            // }
            this.expect("EQ","Expected '='");
            const exp1 = this.expression(0);
            let exp2;
            // if(vars) {
            //     let last = Expr.Lam(vars[vars.length-1],exp1);
            //     for(let i = vars.length-2;i >= 0;i--) {
            //         last = Expr.Lam(vars[i],last);
            //     }
            //     return Expr.Let(name,Expr.Fix(Expr.Lam(name,last)),exp2);
            // }
            const ik = this.peek();
            if(ik && ik.type == "IN") {
                this.consume();
                exp2 = this.expression(0);
            }
            return Expr.Let(name,exp1,exp2);
        }
    },
    "OR": {
        lbp:1,
        nud() {
            this.expect(null,"'or' is not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("OR",left,right);
        }
    },
    "AND": {
        lbp:2,
        nud() {
            this.expect(null,"'and' is not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("AND",left,right);
        }
    },
    "EQ": {
        lbp:3,
        nud() {
            this.expect(null,"'=' is not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("EQ",left,right);
        }
    },
    "GT": {
        lbp:4,
        nud() {
            this.expect(null,"'>' is not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("GT",left,right);
        }
    },
    "LT": {
        lbp:4,
        nud() {
            this.expect(null,"'<' is not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("LT",left,right);
        }
    },
    "MUL": {
        lbp:6,
        nud() {
            this.expect(null,"'*' not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("MUL",left,right);
        }
    },
    "DIV": {
        lbp:6,
        nud() {
            this.expect(null,"'/' not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("DIV",left,right);
        }
    },
    "SUB": {
        rbp:7,
        lbp:5,
        nud() {
            return Expr.UnOp("NEG",this.expression(this.rbp));
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("SUB",left,right);
        }
    },
    "NOT": {
        rbp:7,
        nud() {
            return Expr.UnOp("NOT",this.expression(this.rbp));
        },
        led(left) {
            this.expect(null,`'not' is not a binary operator`);
        }
    },
    "ADD": {
        lbp:5,
        nud() {
            this.expect(null,"'+' not a unary operator");
        },
        led(left) {
            const right = this.expression(this.lbp);
            return Expr.BinOp("ADD",left,right);
        }
    },
    "IF": {
        nud() {
            const cond = this.expression(0);
            this.expect("THEN","Expected keyword 'then'");
            const e1 = this.expression(0);
            this.expect("ELSE","Expected keyword 'else'");
            const e2 = this.expression(0);
            return Expr.Cond(cond,e1,e2);
        },
        led() {
            this.expect(null,"'if' is not a binary operator");
        }
    },
    "LAM": {
        nud() {
            const param = this.expression(0);
            if(!Expr.Var.is(param)) this.expect(null,"Expected an identifier");
            const tok = this.peek();
            if(tok.type === "DEFT") {
                this.consume();
                const type = this.type(":");
                this.expect("BODY","Expected '.'");
                const body = this.expression(0);
                return Expr.Lam(param.name,type,body);
            }
            if(tok.type === "DEFK") {
                this.consume();
                const kind = this.type("::");
                this.expect("BODY","Expected '.'");
                const body = this.type(".");
                return Expr.TCons(param,kind,body);
            }
            this.expect("DEFT","Expected ':' or '::'");
        },
        led() {
            expect(null,"'\\' is not a binary operator");
        }
    },
    "TYPELAM": {
        nud() {
            const param = this.expression(0);
            let kind = "*";
            if(!Expr.Var.is(param)) this.expect(null,"Expected an identifier");
            if(this.peek().type === "DEFK") {
                this.consume();
                kind = this.type("::");
            }
            this.expect("BODY","Expected '.'");
            const body = this.expression(0);
            const node = Expr.TLam(param.name, kind, body);
            return node;
        },
        led() {
            expect(null,"'?' is not a binary operator");
        }
    },
    "LBR": {
        lbp:8,
        nud() {
            this.expect(null,"'[' not a unary operator");
        },
        led(left) {
            const t = this.type("[");
            this.expect("RBR", "Unmatched paren '['");
            return Expr.TApp(left,t);
        }
    },
    "APPLY": {
        lbp:9,
        led(left) {
            if(arguments[1]) {
                const right = this.type("",left);
                return Expr.TCApp(left,right);
            }
            const right = this.expression(this.lbp);
            return Expr.App(left,right);
        }
    }
}

function multiThis(func,...obj) {
    let merged = new Proxy({ all: obj }, {
        set(target,key,value) {
            let o = undefined;
            for(let e of target.all) {
                if(e[key]) {
                    o = e[key] = value;
                    break;
                }
            }
            return o;
        },
        get(target,key) {
            let o = undefined;
            for(let e of target.all) {
                if(e[key]) {
                    o = e[key];
                    break;
                }
            }
            return o;
        }
    });
    return func.bind(merged);
}

class Parser {
    constructor() {}

    consume() {
        return this.tokens.shift();
    }

    peek() {
        return this.tokens[0];
    }

    typePre(curr) {
        if(curr.type === "MUL") return this.consume().value;
        if(curr.type === "IDEN" || curr.type === "TYPE") return this.consume().value;
        if(curr.type === "LPAREN") {
            this.consume();
            const t = this.type("(");
            this.expect("RPAREN","Mismatched '(' in type");
            return t;
        }
        if(curr.type === "FORALL") {
            this.consume();
            const v = this.expect("IDEN","Expected a variable").value;
            let kind = "*";
            if(this.peek().type === "DEFK") {
                this.consume();
                kind = this.type("::");
            }
            this.expect("BODY","Expected '.'");
            const t = this.type(".");
            return { var:v, kind:kind, type:t };
        }
        if(curr.type === "LAM") {
            this.consume();
            const node = multiThis(handlers["LAM"].nud,handlers["LAM"],this)();
            if(!Expr.TCons.is(node)) this.expect(null,"Can only use types or type operators")
            return node;
        }
        this.expect("TYPE",`Expected kind, type or variable'`);
    }

    type(after,def=null) {
        let t = def;
        let token = this.peek();
        t = this.typePre(token);
        token = this.peek();
        while(token.type === "TO" || token.type === "KITO") {
            this.consume();
            t = [t,this.type("")];
            token = this.peek();
        }
        token = this.peek();
        while(!def && !not.includes(token.type) && !ops.includes(token.type) && token.value !== 0) {
            t = multiThis(handlers["APPLY"].led,handlers["APPLY"],this)(t,true);
            token = this.peek();
        }
        if(!t) this.expect("TYPE",`Expected kind, type or variable after '${after}'`);
        return t;
    }

    expect(next, msg) {
        if (next && this.peek().type == next)
            return this.consume();
        throw new Error(msg);
    }

    expression(min,pleft) {
        let left = pleft;
        let token = this.peek();
        if(token.type == "EOF") this.expect(null,"Unexpected end");
        if(handlers[token.type] && !left) {
            token = this.consume();
            left = multiThis(handlers[token.type].nud,handlers[token.type],this)(token);
        }
        token = this.peek();
        while(ops.includes(token.type) && min <= handlers[token.type].lbp && token.value != 0) {
            token = this.consume();
            left = multiThis(handlers[token.type].led,handlers[token.type],this)(left);
            token = this.peek();
        }
        token = this.peek();
        while(!not.includes(token.type) && !ops.includes(token.type) && min < handlers["APPLY"].lbp && token.value !== 0) {
            left = multiThis(handlers["APPLY"].led,handlers["APPLY"],this)(left);
            token = this.peek();
            if(ops.includes(token.type)) left = this.expression(0,left);
        }
        return left;
    }

    parse(str) {
        this.tokens = tokenize(str);
        const e = this.expression(0);
        const token = this.peek();
        if(token.value !== 0 && not.includes(token.type)) this.expect(null,`Unexpected keyword ${token.value}`)
        return e;
    }
}

// const p1 = new Parser();
// console.log(p1.parse("\\x:number. x").toString());
// console.log(p1.parse("\\x::*. x -> x").toString());
// console.log(p1.parse("\\x::*=>*. x number").toString());
// console.log(p1.parse("let Pair = \\x::*. \\y::*. @o. (x -> y -> r) -> r").toString());
// console.log(p1.parse("?a::*. ?b::*. \\x:a. \\y:b. ?r. \\f:t1->t2->r. f x y").toString());
// console.log(p1.parse("let fst = (?t1. ?t2. \\x: (Pair t1 t2). x [t1] (\\e1:t1. \\e2:t2. e1))").toString());
module.exports = Parser;