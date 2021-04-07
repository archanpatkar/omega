const symbols = [
    "(", ")", "\\", ".", "+", "-", "&", "=", "[", "]","<", ">", 
    "=", "/", "*", "->",":", "?",",","$", "@","::","=>","#","|"
];

const types = ["number", "bool", "unit"];
const keywords = [
    "if", "else", "then", "true", "false", "let", "not", "and", 
    "or", "in", "type", "case", "of", "inl", "inr", 
];

const token_name = new Map();
token_name.set("(", "LPAREN");
token_name.set(")", "RPAREN");
token_name.set("[", "LBR");
token_name.set("]", "RBR");
token_name.set("\\", "LAM");
token_name.set(".", "BODY");
token_name.set(":", "DEFT");
token_name.set("::", "DEFK");
token_name.set("+", "ADD");
token_name.set("-", "SUB");
token_name.set("*", "MUL");
token_name.set("/", "DIV");
token_name.set("->", "TO");
token_name.set("=>", "KITO");
token_name.set(">", "GT");
token_name.set("<", "LT");
token_name.set("=", "EQ");
token_name.set("let", "LET");
token_name.set("in", "IN");
token_name.set("if", "IF");
token_name.set("else", "ELSE");
token_name.set("then", "THEN");
token_name.set("not", "NOT");
token_name.set("and", "AND");
token_name.set("or", "OR");
token_name.set("?","TYPELAM");
token_name.set("@","FORALL");

const white = [" ", "\n", "\b", "\t", "\r"];
function isWhite(c) {
    return white.includes(c);
}

const digits = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
function isNumber(c) {
    return digits.includes(c);
}

function isAlphabet(c) {
    if (c) {
        const av = c.charCodeAt(0);
        return av >= "a".charCodeAt(0) && av <= "z".charCodeAt(0) ||
            av >= "A".charCodeAt(0) && av <= "Z".charCodeAt(0);
    }
    return false;
}

function isBool(s) {
    return s == "true" || s == "false";
}

function token(name, value) {
    return { type: name, value: value };
}

function tokenize(string) {
    const tokens = [];
    let ch;
    let curr = 0;
    while (curr < string.length) {
        ch = string[curr]
        if (isWhite(ch)) curr++;
        else if (symbols.includes(ch)) {
            curr++;
            if (ch == "-") {
                if (string[curr] == ">") ch += string[curr++];
                tokens.push(token(token_name.get(ch), ch));
            }
            if (ch == "=") {
                if (string[curr] == ">") ch += string[curr++];
                tokens.push(token(token_name.get(ch), ch));
            }
            else if(ch == ":") {
                if (string[curr] == ":") ch += string[curr++];
                tokens.push(token(token_name.get(ch), ch));
            }
            else tokens.push(token(token_name.get(ch), ch));
        }
        else if (isNumber(ch)) {
            let dot = false
            let n = "" + ch;
            ch = string[++curr];
            if(ch == ".") {
                dot = true;
                n += ch;
                ch = string[++curr];
            }
            while (isNumber(ch)) {
                n += ch;
                ch = string[++curr];
                if(ch == "." && !dot)  {
                    dot = true;
                    n += ch
                    ch = string[++curr];
                }
                else if(ch == "." && dot) throw new Error("Multiple Dots in Number literal");
            }
            tokens.push(token("LIT", parseFloat(n)));
        }
        else if (isAlphabet(ch)|| ch == "_") {
            let n = "" + ch;
            ch = string[++curr];
            while (isAlphabet(ch) || isNumber(ch) || ch == "_") {
                n += ch;
                ch = string[++curr];
            }
            if (isBool(n)) tokens.push(token("LIT", n == "true" ? true : false));
            else if (types.includes(n)) tokens.push(token("TYPE", n));
            else if (keywords.includes(n)) tokens.push(token(token_name.get(n), n));
            else tokens.push(token("IDEN", n));
        }
        else curr++;
    }
    tokens.push(token("EOF",0));
    return tokens;
}

module.exports = tokenize;