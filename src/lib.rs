//! Macromath provides macros which allow convenient calculations with `checked_*`, `wrapping_*` or
//! `saturating_*` behavior.

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{
  fold::Fold,
  parse_macro_input,
  punctuated::Punctuated,
  token::{Dot, Paren, Question},
  Expr, ExprMethodCall, ExprParen, ExprTry,
};

/// Replaces all supported operators in the given expression with their `checked_*` equivalent.
///
/// Each replaced operation is followed by the `?` operator to allow operator chaining.
///
/// # Supported operators
///
/// | Operator | Replacement         |
/// |----------|---------------------|
/// | `a + b`  | `a.checked_add(b)?` |
/// | `a - b`  | `a.checked_sub(b)?` |
/// | `a * b`  | `a.checked_mul(b)?` |
/// | `a / b`  | `a.checked_div(b)?` |
/// | `a % b`  | `a.checked_rem(b)?` |
/// | `a >> b` | `a.checked_shr(b)?` |
/// | `a << b` | `a.checked_shl(b)?` |
/// | `-a`     | `a.checked_neg()?`  |
///
/// # Returns
///
/// The given expression is wrapped with [Option] and returns [Some] if all checked operations in
/// replaced expression return [Some] and [None] otherwise.
///
/// # Note
///
/// The unary `-` (`.neg()`) operator will not be replaced for numeric literals. This allows to
/// write negative literals as before (`-128i8` is valid, but `-(128i8)` is not).
///
/// # Example
///
/// ```
/// use macromath::checked;
///
/// fn calc() -> Option<i8> {
///   Some(100)
/// }
///
/// assert_eq!(Some(1), checked!(1));
/// assert_eq!(Some(1), checked!(0u32 + 1));
/// assert_eq!(Some(50), checked!(calc()? / 2));
/// assert_eq!(None, checked!(i16::MIN - 1));
/// assert_eq!(Some(0), checked!(1u32 - 1));
/// assert_eq!(None, checked!(0u32 - 1));
///
/// assert_eq!(None, checked!(1u32 << 40));
/// assert_eq!(None, checked!(1u32 >> 40));
///
/// assert_eq!(Some(0), checked!(13u32 / 40));
/// assert_eq!(Some(13), checked!(13u32 % 40));
///
/// assert_eq!(None, checked!(3u32 - 9u32 / 4 * 2));
/// assert_eq!(Some(1), checked!(3u32 - 9u32 / 4 * 1));
///
/// assert_eq!(Some(-128), checked!(-128i8));
/// assert_eq!(None, checked!(-(-128i8)));
/// ```
#[proc_macro]
pub fn checked(input: TokenStream) -> TokenStream {
  let expr = parse_macro_input!(input as Expr);
  let output = checked_impl::Replace.fold_expr(expr);
  quote!(
    (|| -> Option<_> { Some(#output) })()
  )
  .into()
}

/// Replaces all supported operators in the given expression with their `wrapping_*` equivalent.
///
/// # Returns
///
/// The same type as the given expression.
///
/// # Supported operators
///
/// | Operator | Replacement         |
/// |----------|---------------------|
/// | `a + b`  | `a.wrapping_add(b)` |
/// | `a - b`  | `a.wrapping_sub(b)` |
/// | `a * b`  | `a.wrapping_mul(b)` |
/// | `a / b`  | `a.wrapping_div(b)` |
/// | `a % b`  | `a.wrapping_rem(b)` |
/// | `a >> b` | `a.wrapping_shr(b)` |
/// | `a << b` | `a.wrapping_shl(b)` |
/// | `-a`     | `a.wrapping_neg()`  |
///
/// # Note
///
/// The unary `-` (`.neg()`) operator will not be replaced for numeric literals. This allows to
/// write negative literals as before (`-128i8` is valid, but `-(128i8)` is not).
///
/// # Example
///
/// ```
/// use macromath::wrapping;
///
/// assert_eq!(1, wrapping!(1));
/// assert_eq!(1, wrapping!(0u32 + 1));
/// assert_eq!(255, wrapping!(1u8 - 2));
/// assert_eq!(127, wrapping!(i8::MIN - 1));
///
/// assert_eq!(0, wrapping!(1u32 << 35));
/// assert_eq!(8, wrapping!(1u32 >> 35));
///
/// assert_eq!(-2, wrapping!(127i8 * 2));
/// assert_eq!(-50, wrapping!(-100i8 / 2));
/// assert_eq!(-128, wrapping!(-128i8 / -1));
///
/// assert_eq!(-128, wrapping!(-128i8));
/// assert_eq!(-128, wrapping!(-(-128i8)));
/// ```
#[proc_macro]
pub fn wrapping(input: TokenStream) -> TokenStream {
  let expr = parse_macro_input!(input as Expr);
  let output = wrapping_impl::Replace.fold_expr(expr);
  quote!(#output).into()
}

/// Replaces all supported operators in the given expression with their `saturating_*` equivalent.
///
/// # Returns
///
/// The same type as the given expression.
///
/// # Supported operators
///
/// | Operator | Replacement           |
/// |----------|-----------------------|
/// | `a + b`  | `a.saturating_add(b)` |
/// | `a - b`  | `a.saturating_sub(b)` |
/// | `a * b`  | `a.saturating_mul(b)` |
/// | `a / b`  | `a.saturating_div(b)` |
/// | `a % b`  | `a.saturating_rem(b)` |
/// | `-a`     | `a.saturating_neg()`  |
///
/// # Note
///
/// The unary `-` (`.neg()`) operator will not be replaced for numeric literals. This allows to
/// write negative literals as before (`-128i8` is valid, but `-(128i8)` is not).
///
/// # Example
///
/// ```
/// use macromath::saturating;
///
/// assert_eq!(1, saturating!(0u32 + 1));
/// assert_eq!(0, saturating!(0u32 - 1));
/// assert_eq!(-128, saturating!(-128i8));
/// assert_eq!(127, saturating!(-(-128i8)));
/// assert_eq!(-128, saturating!(i8::MIN - 1));
///
/// assert_eq!(1, saturating!(1u8));
/// assert_eq!(-128, saturating!(-128i8));
/// assert_eq!(127, saturating!(-(-128i8)));
/// assert_eq!(0, saturating!(1u8 - 2));
/// assert_eq!(127, saturating!(100i8 * 2));
/// ```
#[proc_macro]
pub fn saturating(input: TokenStream) -> TokenStream {
  let expr = parse_macro_input!(input as Expr);
  let output = saturating_impl::Replace.fold_expr(expr);
  quote!(#output).into()
}

mod checked_impl {
  use crate::{try_op_binary, try_op_unary};
  use syn::{
    fold::{self, Fold},
    BinOp, Expr, ExprBinary, ExprUnary, UnOp,
  };

  #[derive(Debug)]
  pub(super) struct Replace;

  impl Fold for Replace {
    fn fold_expr(&mut self, e: Expr) -> Expr {
      fold::fold_expr(
        self,
        match e {
          Expr::Binary(ExprBinary {
            attrs,
            left,
            op,
            right,
          }) => match op {
            BinOp::Add(_) => try_op_binary("checked_add", left, *right),
            BinOp::Sub(_) => try_op_binary("checked_sub", left, *right),
            BinOp::Mul(_) => try_op_binary("checked_mul", left, *right),
            BinOp::Div(_) => try_op_binary("checked_div", left, *right),
            BinOp::Rem(_) => try_op_binary("checked_rem", left, *right),
            BinOp::Shl(_) => try_op_binary("checked_shr", left, *right),
            BinOp::Shr(_) => try_op_binary("checked_shl", left, *right),
            _ => Expr::Binary(ExprBinary {
              attrs,
              left,
              op,
              right,
            }),
          },
          Expr::Unary(ExprUnary { attrs, op, expr }) => match (op, &*expr) {
            (_, Expr::Lit(_)) => Expr::Unary(ExprUnary { attrs, op, expr }),
            (UnOp::Neg(_), _) => try_op_unary("checked_neg", expr),
            _ => Expr::Unary(ExprUnary { attrs, op, expr }),
          },
          _ => e,
        },
      )
    }
  }
}

mod wrapping_impl {
  use crate::{op_binary, op_unary};
  use syn::{
    fold::{self, Fold},
    BinOp, Expr, ExprBinary, ExprUnary, UnOp,
  };

  #[derive(Debug)]
  pub(super) struct Replace;

  impl Fold for Replace {
    fn fold_expr(&mut self, e: Expr) -> Expr {
      fold::fold_expr(
        self,
        match e {
          Expr::Binary(ExprBinary {
            attrs,
            left,
            op,
            right,
          }) => match op {
            BinOp::Add(_) => op_binary("wrapping_add", left, *right),
            BinOp::Sub(_) => op_binary("wrapping_sub", left, *right),
            BinOp::Mul(_) => op_binary("wrapping_mul", left, *right),
            BinOp::Div(_) => op_binary("wrapping_div", left, *right),
            BinOp::Rem(_) => op_binary("wrapping_rem", left, *right),
            BinOp::Shl(_) => op_binary("wrapping_shr", left, *right),
            BinOp::Shr(_) => op_binary("wrapping_shl", left, *right),
            _ => Expr::Binary(ExprBinary {
              attrs,
              left,
              op,
              right,
            }),
          },
          Expr::Unary(ExprUnary { attrs, op, expr }) => match (op, &*expr) {
            (_, Expr::Lit(_)) => Expr::Unary(ExprUnary { attrs, op, expr }),
            (UnOp::Neg(_), _) => op_unary("wrapping_neg", expr),
            _ => Expr::Unary(ExprUnary { attrs, op, expr }),
          },
          _ => e,
        },
      )
    }
  }
}

mod saturating_impl {
  use crate::{op_binary, op_unary};
  use syn::{
    fold::{self, Fold},
    BinOp, Expr, ExprBinary, ExprUnary, UnOp,
  };

  #[derive(Debug)]
  pub(super) struct Replace;

  impl Fold for Replace {
    fn fold_expr(&mut self, e: Expr) -> Expr {
      fold::fold_expr(
        self,
        match e {
          Expr::Binary(ExprBinary {
            attrs,
            left,
            op,
            right,
          }) => match op {
            BinOp::Add(_) => op_binary("saturating_add", left, *right),
            BinOp::Sub(_) => op_binary("saturating_sub", left, *right),
            BinOp::Mul(_) => op_binary("saturating_mul", left, *right),
            BinOp::Div(_) => op_binary("saturating_div", left, *right),
            BinOp::Rem(_) => op_binary("saturating_rem", left, *right),
            _ => Expr::Binary(ExprBinary {
              attrs,
              left,
              op,
              right,
            }),
          },
          Expr::Unary(ExprUnary { attrs, op, expr }) => match (op, &*expr) {
            (_, Expr::Lit(_)) => Expr::Unary(ExprUnary { attrs, op, expr }),
            (UnOp::Neg(_), _) => op_unary("saturating_neg", expr),
            _ => Expr::Unary(ExprUnary { attrs, op, expr }),
          },
          _ => e,
        },
      )
    }
  }
}

fn op_binary(op: &str, left: Box<Expr>, right: Expr) -> Expr {
  use proc_macro2::{Ident, Span};

  Expr::MethodCall(ExprMethodCall {
    attrs: vec![],
    receiver: Box::new(Expr::Paren(ExprParen {
      attrs: vec![],
      paren_token: Paren::default(),
      expr: left,
    })),
    dot_token: Dot::default(),
    method: Ident::new(op, Span::call_site()),
    turbofish: None,
    paren_token: Paren::default(),
    args: Punctuated::from_iter([right]),
  })
}

fn op_unary(op: &str, expr: Box<Expr>) -> Expr {
  use proc_macro2::{Ident, Span};

  Expr::MethodCall(ExprMethodCall {
    attrs: vec![],
    receiver: Box::new(Expr::Paren(ExprParen {
      attrs: vec![],
      paren_token: Paren::default(),
      expr,
    })),
    dot_token: Dot::default(),
    method: Ident::new(op, Span::call_site()),
    turbofish: None,
    paren_token: Paren::default(),
    args: Punctuated::default(),
  })
}

fn try_op_binary(op: &str, left: Box<Expr>, right: Expr) -> Expr {
  use proc_macro2::{Ident, Span};

  Expr::Try(ExprTry {
    attrs: vec![],
    expr: Box::new(Expr::MethodCall(ExprMethodCall {
      attrs: vec![],
      receiver: Box::new(Expr::Paren(ExprParen {
        attrs: vec![],
        paren_token: Paren::default(),
        expr: left,
      })),
      dot_token: Dot::default(),
      method: Ident::new(op, Span::call_site()),
      turbofish: None,
      paren_token: Paren::default(),
      args: Punctuated::from_iter([right]),
    })),
    question_token: Question::default(),
  })
}

fn try_op_unary(op: &str, expr: Box<Expr>) -> Expr {
  use proc_macro2::{Ident, Span};

  Expr::Try(ExprTry {
    attrs: vec![],
    expr: Box::new(Expr::MethodCall(ExprMethodCall {
      attrs: vec![],
      receiver: Box::new(Expr::Paren(ExprParen {
        attrs: vec![],
        paren_token: Paren::default(),
        expr,
      })),
      dot_token: Dot::default(),
      method: Ident::new(op, Span::call_site()),
      turbofish: None,
      paren_token: Paren::default(),
      args: Punctuated::default(),
    })),
    question_token: Question::default(),
  })
}
