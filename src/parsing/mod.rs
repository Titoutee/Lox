use std::collections::HashMap;

use peg;
pub mod expression;
pub use expression::{Identifier, Literal, BinOp, Expression, MonOp};

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Statement {
    VarDeclare(String),
    VarAssign(String, Expression),
    VarReassign(String, Expression),

    Scope {
        body: Vec<Statement>,
    },

    While {
        condition: Expression,
        body: Vec<Statement>,
    },
    
    IfThenElse {
        condition: Expression,
        if_branch: Vec<Statement>,
        else_branch: Option<Vec<Statement>>,
    },

    TopLevelConstruct(TopLevelConstruct),

    Return(Expression),

    ExprSole(Expression),

    Empty,
}

#[derive(Debug, Clone)]
pub struct Var {
    pub literal: Literal,
}

impl Var {
    pub fn from(literal: Literal) -> Self {
        Var { literal }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Function {
    pub params: Vec<String>,
    pub stmts: Vec<Statement>,
}

impl Function {
    pub fn from(params: Vec<Identifier>, stmts: Vec<Statement>) -> Self {
        Function {
            params,
            stmts
        }
    }
}

// Defines a class pattern, ready for instantiation
#[derive(Debug, Clone)]
pub struct Class {
    pub methods: HashMap<Identifier, Function>,
    pub fields: Vec<Identifier>,
}

impl PartialEq for Class {
    fn eq(&self, other: &Self) -> bool {
        self.fields == other.fields && self.methods.len() == other.methods.len()
    }
}

impl Class {
    pub fn new() -> Self {
        Class {
            methods: HashMap::new(),
            fields: vec![],
        }
    }

    pub fn add_method(&mut self,id: Identifier, method: Function) {
        self.methods.insert(id, method);
    }

    pub fn add_field(&mut self, field: Identifier) {
        self.fields.push(field);
    }
}

pub enum ExecRes {
    Normal,
    Result(Literal),
}

#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum TopLevelConstruct {
    Class(String, Vec<Statement>),
    Function(String, Vec<String>, Vec<Statement>),
}

#[derive(Debug, Clone)]
pub struct Object<'a> {
    class_pattern: &'a Class,
    private_fields: Vec<Identifier>,
}

impl<'a> Object<'a> {
    pub fn from_pattern(r: &'a Class) -> Self {
        Object { class_pattern: r, private_fields: vec![]}
    }
}

impl<'a> PartialEq for Object<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.class_pattern == other.class_pattern && self.private_fields == other.private_fields
    }
}

// Dummy implementation, only for Literal compliance
impl<'a> PartialOrd for Object<'a> {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        None
    }
}

peg::parser! {
    pub grammar ast_parser() for str {
        rule _ = quiet!{[' ' | '\n' | '\t']*}

        rule identifier() -> Identifier
            = _ s:$((['a'..='z' | 'A'..='Z' | '_'])+) _ {s.to_owned()}

        rule literal_string() -> Literal
            = "\"" s:identifier() "\"" {Literal::String(s.to_owned())}

        rule literal_number() -> Literal // Only scalar type in Lox is f64
            = n:$(['0'..='9']+ ("." ['0'..='9']*)?) {?
                let inner = {n.parse::<f64>().or(Err("f64"))?};
                Ok(Literal::Number(inner))
            }
            
        rule literal_bool() -> Literal
            = s:identifier() {?
                match s.as_str() {
                    "True" => Ok(Literal::Bool(true)),
                    "False" => Ok(Literal::Bool(false)),
                    _ => Err("bool"),
                }
            }

        pub(super) rule literal() -> Literal
            = literal_number() / literal_string() / literal_bool()

        // Statements
        pub (super) rule expr_sole() -> Expression
            = _ e:expression() _ { e }

        pub(super) rule var_declare() -> Identifier
            = "var" _ i:identifier() _ {i}

        pub(super) rule var_init() -> (Identifier, Expression)
            = d:var_declare() _ "=" _ e:expression() _ {(d, e)}

        pub (super) rule var_reassign() -> (Identifier, Expression)
            = i:identifier() _ "=" _ e:expression() _ {(i, e)}

        // Used for functions and classes inner statements parsing
        rule inner_statements() -> Vec<Statement>
            = _ s:statement() ** _ {s}
        
        rule string_pack()
            = _ s:identifier() ** _

        rule scope() -> Vec<Statement>
            = "{" _ s:inner_statements() _ "}" _ {s}
        
        rule comment()
            = "//" string_pack() "//"

        rule param_and_args() -> Vec<String>
            = s:$(identifier()+) ** (_ "," _) {s.into_iter().map(|slice| slice.to_owned()).collect()}

        pub(super) rule class() -> (Identifier, Vec<Statement>, Option<Identifier>)
            = "class" _ c:identifier() p:(_ "<" _ p:identifier() {p})? _ stmts:scope() {(c.to_owned(), stmts, p)}

        pub(super) rule function_def() -> (String, Function)
            = "fun" _ f:identifier() "(" a:param_and_args() ")" _ stmts:scope() {(f, Function::from(a, stmts))}
        
        pub(super) rule while_() -> (Expression, Vec<Statement>)
            = "while" _ "(" _ e:expression() _ ")" _ stmts:scope() {(e, stmts)}
        
        pub(super) rule ret() -> Expression
            = "return" _ e:expression() _ {e}
        
        pub(super) rule if_then_else() -> (Expression, Vec<Statement>, Option<Vec<Statement>>) // "condition";"ifStmts";"elseStatements"
            = "if" _ "(" _ e:expression() _ ")" _ "{" _ i_s:inner_statements() _ "}" _ e_s:("else" _ "{" _ es:inner_statements() _ "}" {es})? _  {(e, i_s, e_s)}

        
        // Core
        pub(super) rule expression() -> Expression
                = precedence! {
                x:(@) _ "||" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Or }}
                x:(@) _ "&&" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::And }}
                x:(@) _ "//" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::XOr }}
                --
                x:(@) _ "==" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Eq }}
                x:(@) _ ">=" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Ge }}
                x:(@) _ "<=" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Le }}
                x:(@) _ ">" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Gt }}
                x:(@) _ "<" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Lt }}
                --
                x:(@) _ "+" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Plus }}
                x:(@) _ "-" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Minus }}
                --
                x:(@) _ "*" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Mul }}
                x:(@) _ "/" _ y:@ {Expression::BinOperation { lhs: Box::new(x), rhs: Box::new(y), operator: BinOp::Div }}
                --
                "-" _ y:@ {Expression::UnaryOp { operation: MonOp::Minus, operand: Box::new(y) }}
                "!" _ y:@ {Expression::UnaryOp { operation: MonOp::Not, operand: Box::new(y) }}
                --
                "(" _ e:expression() _ ")" { e }
                i:identifier() "(" _ args:expression() ** (_ "," _) _ ")" { Expression::FunctionCall { function_name: i, arguments: args } }
                // i:identifier() { Expression::Object { class_name: i.to_owned() }}
                // i:identifier() "." f:identifier() { Expression::ObjectField { class_name: i.to_owned(), field: f.to_owned() }}
                // Atoms = max precedence level
                l:literal() { Expression::Literal(l) }
                i:identifier() { Expression::Var(i) }
            }

        pub(super) rule statement() -> Statement
            = i:var_init() ";" _ { Statement::VarAssign(i.0, i.1) }
              / e:var_declare() ";" _ { Statement::VarDeclare(e) }
              / a:var_reassign() ";" _ { Statement::VarReassign(a.0, a.1)}
              / r:ret() ";" _ { Statement::Return(r) }
              / e:expr_sole() ";" _ { Statement::ExprSole(e) }
              / _ comment() _ { Statement::Empty }
              / c:class() _ { Statement::TopLevelConstruct(TopLevelConstruct::Class(c.0, c.1)) }
              / f:function_def() _ { Statement::TopLevelConstruct(TopLevelConstruct::Function(f.0, f.1.params, f.1.stmts)) }
              / w:while_() _ { Statement::While { condition: w.0, body: w.1 } }
              / i:if_then_else() _ { Statement::IfThenElse { condition: i.0, if_branch: i.1, else_branch: i.2 } } 
              / s:scope() _ { Statement::Scope { body: s }}
        
        // Core parsing procedure
        pub rule parse() -> Vec<Statement>
            = _ stmts:statement() ** _ {stmts}
    }
}

#[cfg(test)]
mod tests {
    use super::{Expression, Function, Literal};
    use crate::parsing::{ast_parser, BinOp, MonOp, Statement};

    #[test]
    fn var_empty() {
        let var_empty = "var compound;";
        match ast_parser::statement(var_empty).unwrap() {
            Statement::VarDeclare(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    fn var_empty_ill() {
        let var_empty = "var compound ;";
        match ast_parser::statement(var_empty).unwrap() {
            Statement::VarDeclare(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    #[should_panic]
    fn var_empty_bad() {
        let var_empty = "va r compou nd;"; // Badly formed
        match ast_parser::statement(var_empty).unwrap() {
            Statement::VarDeclare(id) => {
                assert_eq!(id, String::from("compound"));
            }
            _ => panic!("Uninit should not contain a literal!"),
        }
    }

    #[test]
    fn literal_string() {
        let string = "\"hey\"";
        match ast_parser::literal(string).unwrap() {
            Literal::String(s) => {
                assert_eq!(s, String::from("hey"));
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn literal_number() {
        let number = "6543";
        match ast_parser::literal(number).unwrap() {
            Literal::Number(n) => {
                assert_eq!(n, 6543.);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn literal_bool() {
        let bool_1 = "True";
        let bool_2 = "False";
        //let bad_bool = "jhkjhdf";
        match ast_parser::literal(bool_1).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, true);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
        match ast_parser::literal(bool_2).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, false);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    #[should_panic]
    fn literal_bool_bad() {
        let bool = "sdkjfsdf";
        //let bad_bool = "jhkjhdf";
        match ast_parser::literal(bool).unwrap() {
            Literal::Bool(n) => {
                assert_eq!(n, true);
            }
            _ => panic!("Did not expect anything other than a string!"),
        }
    }

    #[test]
    fn var_init() {
        let var_init = "var compound = 12;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Number(number_literal)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(number_literal, 12.);
            }
            _ => panic!("Not a string, but better a number!"),
        }
    }

    #[test]
    fn var_init_bool_true() {
        let var_init = "var compound = True;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Bool(b)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(b, true);
            }
            _ => panic!("Not a var assign"),
        }
    }

    #[test]
    fn var_init_bool_false() {
        let var_init = "var compound = False;";
        //assert_eq!(ast_parser::var_init(var_init).unwrap(), String::from("compound"));
        match ast_parser::statement(var_init).unwrap() {
            Statement::VarAssign(id, Expression::Literal(Literal::Bool(b)) ) => {
                assert_eq!(id, String::from("compound"));
                assert_eq!(b, false);
            }
            _ => panic!("Not a var assign"),
        }
    }

    #[test]
    fn class() {
        let class_def = "class Heya {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::class(class_def).unwrap() {
            (id, statements, parent) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(
                    statements,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string()
                        ))),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
                assert_eq!(parent, None)
            }
        }
    }

    #[test]
    fn class_inherit() {
        let class_def = "class Heya < OtherClass {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::class(class_def).unwrap() {
            (id, statements, parent) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(
                    statements,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string()
                        ))),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
                assert_eq!(parent, Some(String::from("OtherClass")));
            }
        }
    }

    #[test]
    fn function() {
        let fun_def = "fun Heya(hey) {
            var init = 12;
            var lol = \"hey\";
            var empty;
        }";

        match ast_parser::function_def(fun_def).unwrap() {
            (id, Function { params, stmts }) => {
                assert_eq!(id, String::from("Heya"));
                assert_eq!(params, vec![String::from("hey")]);
                assert_eq!(
                    stmts,
                    vec![
                        Statement::VarAssign("init".to_string(), Expression::Literal(Literal::Number(12.0))),
                        Statement::VarAssign(
                            "lol".to_string(),
                            Expression::Literal(Literal::String("hey".to_string())
                        )),
                        Statement::VarDeclare("empty".to_string())
                    ]
                );
            }
        }
    }

    #[test]
    fn expression_1() {
        let expr = "1+2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Plus })
    }

    #[test]
    fn expression_2() {
        let expr = "1*2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Mul })
    }

    #[test]
    fn expression_3() {
        let expr = "1/2";
        let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs, rhs, operator: crate::parsing::BinOp::Div })
    }

    // Unary ops tests
    #[test]
    fn expression_4() {
        let expr = "-2";
        //let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::UnaryOp { operation: MonOp::Minus, operand: rhs })
    }

    #[test]
    fn expression_5() { // !(Literal::Number) should not work normally, but here parsing only is tested
        let expr = "!2";
        //let lhs = Box::new(Expression::Literal(Literal::Number(1.)));
        let rhs = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::UnaryOp { operation: MonOp::Not, operand: rhs })
    }

    // Precedence tests
    #[test]
    fn expression_6() {
        let expr = "1+2*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: op_1, rhs: Box::new(Expression::BinOperation { lhs: op_2, rhs: op_3, operator: BinOp::Mul }), operator: crate::parsing::BinOp::Plus })
    }
    
    #[test]
    fn expression_7() {
        let expr = "(1+2)*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: Box::new(Expression::BinOperation { lhs: op_1, rhs: op_2, operator: BinOp::Plus }), rhs: op_3, operator: crate::parsing::BinOp::Mul })
    }

    #[test]
    fn expression_8() {
        let expr = "(1+2*3)*3";
        let op_1: Box<Expression> = Box::new(Expression::Literal(Literal::Number(1.)));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        let op_3 = Box::new(Expression::Literal(Literal::Number(3.)));
        let op_4 = Box::new(Expression::Literal(Literal::Number(3.)));
        
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: Box::new(Expression::BinOperation { lhs: op_1, rhs: Box::new(Expression::BinOperation { lhs: op_2, rhs: op_3, operator: BinOp::Mul }), operator: BinOp::Plus }), rhs: op_4, operator: crate::parsing::BinOp::Mul })
    }

    // Variable integration tests
    #[test]
    fn expression_9() {
        let expr = "a+2";
        let op_1: Box<Expression> = Box::new(Expression::Var(String::from("a")));
        let op_2 = Box::new(Expression::Literal(Literal::Number(2.)));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), Expression::BinOperation { lhs: op_1, rhs: op_2, operator: BinOp::Plus })
    }

    #[test]
    fn expression_11() {
        let expr = "a";
        //let op_1: Box<Expression> = Box::new(Expression::Var(String::from("a")));
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(),  Expression::Var(String::from("a")));
    }

    // Function calls and object building
    #[test]
    fn expression_10() {
        let expr = "hey(4, a)";
        let op_1: Expression = Expression::FunctionCall { function_name: String::from("hey"), arguments: vec![Expression::Literal(Literal::Number(4.)), Expression::Var(String::from("a"))] };
        //println!("{:?}", ast_parser::expression(expr).unwrap());
        assert_eq!(ast_parser::expression(expr).unwrap(), op_1)
    }
}
