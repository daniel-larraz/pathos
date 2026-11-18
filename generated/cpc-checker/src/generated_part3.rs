//! Generated functions, module 3 of 12.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn if_120_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1428 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1429 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1430 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1437 = match if_118_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1438 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1439 = match s.literal(Lit::Numeral(v1438)) { Ok(v) => v, Err(e) => return Err(e) };
let v1440 = match s.builtin_list(EvalOp::ListNth, &[v1430, v1437, v1439]) { Ok(v) => v, Err(e) => return Err(e) };
let v1441 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1429, v1440]) { Ok(v) => v, Err(e) => return Err(e) };
let v1442 = match eo__24str_5fflatten(s, v1441) { Ok(v) => v, Err(e) => return Err(e) };
let v1443 = match s.builtin_list(EvalOp::ListRev, &[v1428, v1442]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1443)
}
Some(false) => {
let v1444 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1445 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1452 = match if_119_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1453 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1454 = match s.literal(Lit::Numeral(v1453)) { Ok(v) => v, Err(e) => return Err(e) };
let v1455 = match s.builtin_list(EvalOp::ListNth, &[v1445, v1452, v1454]) { Ok(v) => v, Err(e) => return Err(e) };
let v1456 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1444, v1455]) { Ok(v) => v, Err(e) => return Err(e) };
let v1457 = match eo__24str_5fflatten(s, v1456) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1457)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_121_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1471 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1472 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1473 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1472, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1474 = match s.builtin_list(EvalOp::ListRev, &[v1471, v1473]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1474)
}
Some(false) => {
let v1475 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1476 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1475, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1476)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_122_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1490 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1491 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1492 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1491, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1493 = match s.builtin_list(EvalOp::ListRev, &[v1490, v1492]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1493)
}
Some(false) => {
let v1494 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1495 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1494, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1495)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_123_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1503 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1504 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1505 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1504, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1506 = match s.builtin_list(EvalOp::ListRev, &[v1503, v1505]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1506)
}
Some(false) => {
let v1507 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1508 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1507, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1508)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_124_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1519 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1520 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1521 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1520, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1522 = match s.builtin_list(EvalOp::ListRev, &[v1519, v1521]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1522)
}
Some(false) => {
let v1523 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1524 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1523, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1524)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_125_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1532 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1533 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1534 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1533, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1535 = match s.builtin_list(EvalOp::ListRev, &[v1532, v1534]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1535)
}
Some(false) => {
let v1536 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1537 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1536, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1537)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_126_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1489 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1496 = match if_122_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1497 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1498 = match s.literal(Lit::Numeral(v1497)) { Ok(v) => v, Err(e) => return Err(e) };
let v1499 = match s.builtin_list(EvalOp::ListNth, &[v1489, v1496, v1498]) { Ok(v) => v, Err(e) => return Err(e) };
let v1500 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1501 = match s.literal(Lit::Numeral(v1500)) { Ok(v) => v, Err(e) => return Err(e) };
let v1502 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1509 = match if_123_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1510 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1511 = match s.literal(Lit::Numeral(v1510)) { Ok(v) => v, Err(e) => return Err(e) };
let v1512 = match s.builtin_list(EvalOp::ListNth, &[v1502, v1509, v1511]) { Ok(v) => v, Err(e) => return Err(e) };
let v1513 = match s.builtin_core(EvalOp::Length, &[v1512]) { Ok(v) => v, Err(e) => return Err(e) };
let v1514 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1515 = match s.literal(Lit::Numeral(v1514)) { Ok(v) => v, Err(e) => return Err(e) };
let v1516 = match s.builtin_core(EvalOp::Add, &[v1513, v1515]) { Ok(v) => v, Err(e) => return Err(e) };
let v1517 = match s.builtin_core(EvalOp::Extract, &[v1499, v1501, v1516]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1517)
}
Some(false) => {
let v1518 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1525 = match if_124_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1526 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1527 = match s.literal(Lit::Numeral(v1526)) { Ok(v) => v, Err(e) => return Err(e) };
let v1528 = match s.builtin_list(EvalOp::ListNth, &[v1518, v1525, v1527]) { Ok(v) => v, Err(e) => return Err(e) };
let v1529 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1530 = match s.literal(Lit::Numeral(v1529)) { Ok(v) => v, Err(e) => return Err(e) };
let v1531 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1538 = match if_125_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1539 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1540 = match s.literal(Lit::Numeral(v1539)) { Ok(v) => v, Err(e) => return Err(e) };
let v1541 = match s.builtin_list(EvalOp::ListNth, &[v1531, v1538, v1540]) { Ok(v) => v, Err(e) => return Err(e) };
let v1542 = match s.builtin_core(EvalOp::Length, &[v1541]) { Ok(v) => v, Err(e) => return Err(e) };
let v1543 = match s.builtin_core(EvalOp::Extract, &[v1528, v1530, v1542]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1543)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_127_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1550 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1551 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1552 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1551, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1553 = match s.builtin_list(EvalOp::ListRev, &[v1550, v1552]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1553)
}
Some(false) => {
let v1554 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1555 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1554, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1555)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_128_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1563 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1564 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1565 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1564, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1566 = match s.builtin_list(EvalOp::ListRev, &[v1563, v1565]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1566)
}
Some(false) => {
let v1567 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1568 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1567, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1568)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_129_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1579 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1580 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1581 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1580, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1582 = match s.builtin_list(EvalOp::ListRev, &[v1579, v1581]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1582)
}
Some(false) => {
let v1583 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1584 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1583, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1584)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_130_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1592 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1593 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1594 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1593, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1595 = match s.builtin_list(EvalOp::ListRev, &[v1592, v1594]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1595)
}
Some(false) => {
let v1596 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1597 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1596, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1597)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_131_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1549 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1556 = match if_127_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1557 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1558 = match s.literal(Lit::Numeral(v1557)) { Ok(v) => v, Err(e) => return Err(e) };
let v1559 = match s.builtin_list(EvalOp::ListNth, &[v1549, v1556, v1558]) { Ok(v) => v, Err(e) => return Err(e) };
let v1560 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1561 = match s.literal(Lit::Numeral(v1560)) { Ok(v) => v, Err(e) => return Err(e) };
let v1562 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1569 = match if_128_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1570 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1571 = match s.literal(Lit::Numeral(v1570)) { Ok(v) => v, Err(e) => return Err(e) };
let v1572 = match s.builtin_list(EvalOp::ListNth, &[v1562, v1569, v1571]) { Ok(v) => v, Err(e) => return Err(e) };
let v1573 = match s.builtin_core(EvalOp::Length, &[v1572]) { Ok(v) => v, Err(e) => return Err(e) };
let v1574 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1575 = match s.literal(Lit::Numeral(v1574)) { Ok(v) => v, Err(e) => return Err(e) };
let v1576 = match s.builtin_core(EvalOp::Add, &[v1573, v1575]) { Ok(v) => v, Err(e) => return Err(e) };
let v1577 = match s.builtin_core(EvalOp::Extract, &[v1559, v1561, v1576]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1577)
}
Some(false) => {
let v1578 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1585 = match if_129_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1586 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1587 = match s.literal(Lit::Numeral(v1586)) { Ok(v) => v, Err(e) => return Err(e) };
let v1588 = match s.builtin_list(EvalOp::ListNth, &[v1578, v1585, v1587]) { Ok(v) => v, Err(e) => return Err(e) };
let v1589 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1590 = match s.literal(Lit::Numeral(v1589)) { Ok(v) => v, Err(e) => return Err(e) };
let v1591 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1598 = match if_130_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1599 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1600 = match s.literal(Lit::Numeral(v1599)) { Ok(v) => v, Err(e) => return Err(e) };
let v1601 = match s.builtin_list(EvalOp::ListNth, &[v1591, v1598, v1600]) { Ok(v) => v, Err(e) => return Err(e) };
let v1602 = match s.builtin_core(EvalOp::Length, &[v1601]) { Ok(v) => v, Err(e) => return Err(e) };
let v1603 = match s.builtin_core(EvalOp::Extract, &[v1588, v1590, v1602]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1603)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_132_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1487 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1488 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1544 = match if_126_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1545 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1488, v1544]) { Ok(v) => v, Err(e) => return Err(e) };
let v1546 = match eo__24str_5fflatten(s, v1545) { Ok(v) => v, Err(e) => return Err(e) };
let v1547 = match s.builtin_list(EvalOp::ListRev, &[v1487, v1546]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1547)
}
Some(false) => {
let v1548 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1604 = match if_131_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1605 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1548, v1604]) { Ok(v) => v, Err(e) => return Err(e) };
let v1606 = match eo__24str_5fflatten(s, v1605) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1606)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_133_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1611 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1612 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1613 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1612, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1614 = match s.builtin_list(EvalOp::ListRev, &[v1611, v1613]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1614)
}
Some(false) => {
let v1615 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1616 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1615, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1616)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_134_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1626 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1627 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1628 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1627, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1629 = match s.builtin_list(EvalOp::ListRev, &[v1626, v1628]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1629)
}
Some(false) => {
let v1630 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1631 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1630, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1631)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_135_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1608 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1609 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1610 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1617 = match if_133_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1618 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1619 = match s.literal(Lit::Numeral(v1618)) { Ok(v) => v, Err(e) => return Err(e) };
let v1620 = match s.builtin_list(EvalOp::ListNth, &[v1610, v1617, v1619]) { Ok(v) => v, Err(e) => return Err(e) };
let v1621 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1609, v1620]) { Ok(v) => v, Err(e) => return Err(e) };
let v1622 = match eo__24str_5fflatten(s, v1621) { Ok(v) => v, Err(e) => return Err(e) };
let v1623 = match s.builtin_list(EvalOp::ListRev, &[v1608, v1622]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1623)
}
Some(false) => {
let v1624 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1625 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1632 = match if_134_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1633 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1634 = match s.literal(Lit::Numeral(v1633)) { Ok(v) => v, Err(e) => return Err(e) };
let v1635 = match s.builtin_list(EvalOp::ListNth, &[v1625, v1632, v1634]) { Ok(v) => v, Err(e) => return Err(e) };
let v1636 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1624, v1635]) { Ok(v) => v, Err(e) => return Err(e) };
let v1637 = match eo__24str_5fflatten(s, v1636) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1637)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_136_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1650 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1651 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1652 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1651, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1653 = match s.builtin_list(EvalOp::ListRev, &[v1650, v1652]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1653)
}
Some(false) => {
let v1654 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1655 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1654, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1655)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_137_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1669 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1670 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1671 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1670, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1672 = match s.builtin_list(EvalOp::ListRev, &[v1669, v1671]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1672)
}
Some(false) => {
let v1673 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1674 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1673, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1674)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_138_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1682 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1683 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1684 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1683, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1685 = match s.builtin_list(EvalOp::ListRev, &[v1682, v1684]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1685)
}
Some(false) => {
let v1686 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1687 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1686, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1687)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_139_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1698 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1699 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1700 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1699, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1701 = match s.builtin_list(EvalOp::ListRev, &[v1698, v1700]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1701)
}
Some(false) => {
let v1702 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1703 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1702, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1703)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_140_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1711 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1712 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1713 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1712, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1714 = match s.builtin_list(EvalOp::ListRev, &[v1711, v1713]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1714)
}
Some(false) => {
let v1715 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1716 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1715, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1716)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_141_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1668 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1675 = match if_137_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1676 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1677 = match s.literal(Lit::Numeral(v1676)) { Ok(v) => v, Err(e) => return Err(e) };
let v1678 = match s.builtin_list(EvalOp::ListNth, &[v1668, v1675, v1677]) { Ok(v) => v, Err(e) => return Err(e) };
let v1679 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1680 = match s.literal(Lit::Numeral(v1679)) { Ok(v) => v, Err(e) => return Err(e) };
let v1681 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1688 = match if_138_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1689 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1690 = match s.literal(Lit::Numeral(v1689)) { Ok(v) => v, Err(e) => return Err(e) };
let v1691 = match s.builtin_list(EvalOp::ListNth, &[v1681, v1688, v1690]) { Ok(v) => v, Err(e) => return Err(e) };
let v1692 = match s.builtin_core(EvalOp::Length, &[v1691]) { Ok(v) => v, Err(e) => return Err(e) };
let v1693 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1694 = match s.literal(Lit::Numeral(v1693)) { Ok(v) => v, Err(e) => return Err(e) };
let v1695 = match s.builtin_core(EvalOp::Add, &[v1692, v1694]) { Ok(v) => v, Err(e) => return Err(e) };
let v1696 = match s.builtin_core(EvalOp::Extract, &[v1678, v1680, v1695]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1696)
}
Some(false) => {
let v1697 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1704 = match if_139_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1705 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1706 = match s.literal(Lit::Numeral(v1705)) { Ok(v) => v, Err(e) => return Err(e) };
let v1707 = match s.builtin_list(EvalOp::ListNth, &[v1697, v1704, v1706]) { Ok(v) => v, Err(e) => return Err(e) };
let v1708 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1709 = match s.literal(Lit::Numeral(v1708)) { Ok(v) => v, Err(e) => return Err(e) };
let v1710 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1717 = match if_140_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1718 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1719 = match s.literal(Lit::Numeral(v1718)) { Ok(v) => v, Err(e) => return Err(e) };
let v1720 = match s.builtin_list(EvalOp::ListNth, &[v1710, v1717, v1719]) { Ok(v) => v, Err(e) => return Err(e) };
let v1721 = match s.builtin_core(EvalOp::Length, &[v1720]) { Ok(v) => v, Err(e) => return Err(e) };
let v1722 = match s.builtin_core(EvalOp::Extract, &[v1707, v1709, v1721]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1722)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_142_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1729 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1730 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1731 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1730, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1732 = match s.builtin_list(EvalOp::ListRev, &[v1729, v1731]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1732)
}
Some(false) => {
let v1733 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1734 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1733, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1734)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_143_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1742 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1743 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1744 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1743, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1745 = match s.builtin_list(EvalOp::ListRev, &[v1742, v1744]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1745)
}
Some(false) => {
let v1746 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1747 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1746, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1747)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_144_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1758 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1759 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1760 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1759, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1761 = match s.builtin_list(EvalOp::ListRev, &[v1758, v1760]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1761)
}
Some(false) => {
let v1762 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1763 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1762, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1763)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_145_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1771 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1772 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1773 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1772, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1774 = match s.builtin_list(EvalOp::ListRev, &[v1771, v1773]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1774)
}
Some(false) => {
let v1775 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1776 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1775, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1776)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_146_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1728 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1735 = match if_142_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1736 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1737 = match s.literal(Lit::Numeral(v1736)) { Ok(v) => v, Err(e) => return Err(e) };
let v1738 = match s.builtin_list(EvalOp::ListNth, &[v1728, v1735, v1737]) { Ok(v) => v, Err(e) => return Err(e) };
let v1739 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1740 = match s.literal(Lit::Numeral(v1739)) { Ok(v) => v, Err(e) => return Err(e) };
let v1741 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1748 = match if_143_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1749 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1750 = match s.literal(Lit::Numeral(v1749)) { Ok(v) => v, Err(e) => return Err(e) };
let v1751 = match s.builtin_list(EvalOp::ListNth, &[v1741, v1748, v1750]) { Ok(v) => v, Err(e) => return Err(e) };
let v1752 = match s.builtin_core(EvalOp::Length, &[v1751]) { Ok(v) => v, Err(e) => return Err(e) };
let v1753 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1754 = match s.literal(Lit::Numeral(v1753)) { Ok(v) => v, Err(e) => return Err(e) };
let v1755 = match s.builtin_core(EvalOp::Add, &[v1752, v1754]) { Ok(v) => v, Err(e) => return Err(e) };
let v1756 = match s.builtin_core(EvalOp::Extract, &[v1738, v1740, v1755]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1756)
}
Some(false) => {
let v1757 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1764 = match if_144_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1765 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1766 = match s.literal(Lit::Numeral(v1765)) { Ok(v) => v, Err(e) => return Err(e) };
let v1767 = match s.builtin_list(EvalOp::ListNth, &[v1757, v1764, v1766]) { Ok(v) => v, Err(e) => return Err(e) };
let v1768 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1769 = match s.literal(Lit::Numeral(v1768)) { Ok(v) => v, Err(e) => return Err(e) };
let v1770 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1777 = match if_145_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1778 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1779 = match s.literal(Lit::Numeral(v1778)) { Ok(v) => v, Err(e) => return Err(e) };
let v1780 = match s.builtin_list(EvalOp::ListNth, &[v1770, v1777, v1779]) { Ok(v) => v, Err(e) => return Err(e) };
let v1781 = match s.builtin_core(EvalOp::Length, &[v1780]) { Ok(v) => v, Err(e) => return Err(e) };
let v1782 = match s.builtin_core(EvalOp::Extract, &[v1767, v1769, v1781]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1782)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_147_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1666 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1667 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1723 = match if_141_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1724 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1667, v1723]) { Ok(v) => v, Err(e) => return Err(e) };
let v1725 = match eo__24str_5fflatten(s, v1724) { Ok(v) => v, Err(e) => return Err(e) };
let v1726 = match s.builtin_list(EvalOp::ListRev, &[v1666, v1725]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1726)
}
Some(false) => {
let v1727 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1783 = match if_146_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1784 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1727, v1783]) { Ok(v) => v, Err(e) => return Err(e) };
let v1785 = match eo__24str_5fflatten(s, v1784) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1785)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_148_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1790 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1791 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1792 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1791, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1793 = match s.builtin_list(EvalOp::ListRev, &[v1790, v1792]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1793)
}
Some(false) => {
let v1794 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1795 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1794, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1795)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_149_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1805 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1806 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1807 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1806, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1808 = match s.builtin_list(EvalOp::ListRev, &[v1805, v1807]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1808)
}
Some(false) => {
let v1809 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1810 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1809, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1810)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_150_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1787 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1788 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1789 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1796 = match if_148_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1797 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1798 = match s.literal(Lit::Numeral(v1797)) { Ok(v) => v, Err(e) => return Err(e) };
let v1799 = match s.builtin_list(EvalOp::ListNth, &[v1789, v1796, v1798]) { Ok(v) => v, Err(e) => return Err(e) };
let v1800 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1788, v1799]) { Ok(v) => v, Err(e) => return Err(e) };
let v1801 = match eo__24str_5fflatten(s, v1800) { Ok(v) => v, Err(e) => return Err(e) };
let v1802 = match s.builtin_list(EvalOp::ListRev, &[v1787, v1801]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1802)
}
Some(false) => {
let v1803 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1804 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1811 = match if_149_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1812 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1813 = match s.literal(Lit::Numeral(v1812)) { Ok(v) => v, Err(e) => return Err(e) };
let v1814 = match s.builtin_list(EvalOp::ListNth, &[v1804, v1811, v1813]) { Ok(v) => v, Err(e) => return Err(e) };
let v1815 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1803, v1814]) { Ok(v) => v, Err(e) => return Err(e) };
let v1816 = match eo__24str_5fflatten(s, v1815) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1816)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != v5 { return Ok(None); }
Ok(Some(Next::Again([v2, v9])))
}
pub(super) fn if_0_eo__24str_5fis_5fcompatible(s: &mut Store, condition: Term, v5: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24are_5fdistinct_5fterms_5ftype(s, v5, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24str_5fis_5fcompatible(s: &mut Store, v18: Term, v19: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_1_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.builtin_core(EvalOp::Eq, &[v5, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_0_eo__24str_5fis_5fcompatible(s, v14, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_1_eo__24str_5fis_5fcompatible(s, v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v21)))
}
pub(super) fn case_2_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24str_5fis_5fempty(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Or, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn step_eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fis_5fcompatible(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fis_5fcompatible(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fis_5fcompatible(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_is_compatible"
pub fn eo__24str_5fis_5fcompatible(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1047), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fis_5fcompatible(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1047), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(v0)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$str_overlap_rec"
pub fn eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1062), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5foverlap_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1062), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5foverlap_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5foverlap_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5foverlap_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24str_5fis_5fcompatible(s, v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match if_0_eo__24str_5foverlap_5frec(s, v10, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn if_0_eo__24str_5foverlap_5frec(s: &mut Store, condition: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
Some(false) => {
let v13 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24str_5foverlap_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_153_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, v7: Term, v1786: Term, v1665: Term, v1663: Term, v1647: Term, v1646: Term, v1283: Term) -> CheckResult<Term> {
let v1817 = match if_150_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1818 = match eo__24str_5foverlap_5frec(s, v1786, v1817) { Ok(v) => v, Err(e) => return Err(e) };
let v1819 = match s.builtin_core(EvalOp::Add, &[v1665, v1818]) { Ok(v) => v, Err(e) => return Err(e) };
let v1820 = match s.apply(v1663, v1819) { Ok(v) => v, Err(e) => return Err(e) };
let v1821 = match eo__24eo_5ftypeof(s, v1820) { Ok(v) => v, Err(e) => return Err(e) };
let v1822 = match eo__24eo_5fnil(s, v1647, v1821) { Ok(v) => v, Err(e) => return Err(e) };
let v1823 = match s.apply(v1646, v1822) { Ok(v) => v, Err(e) => return Err(e) };
let v1824 = match s.apply(v1283, v1823) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1824)
}
pub(super) fn more_152_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1481: Term, a0: Term, v4: Term, v7: Term, v1468: Term, v1467: Term, v1463: Term, v1285: Term, v1284: Term, v1283: Term) -> CheckResult<Term> {
let v1482 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1483 = match s.literal(Lit::Numeral(v1482)) { Ok(v) => v, Err(e) => return Err(e) };
let v1484 = match s.apply(v1481, v1483) { Ok(v) => v, Err(e) => return Err(e) };
let v1485 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1486 = match s.literal(Lit::Numeral(v1485)) { Ok(v) => v, Err(e) => return Err(e) };
let v1607 = match if_132_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1638 = match if_135_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1639 = match eo__24str_5foverlap_5frec(s, v1607, v1638) { Ok(v) => v, Err(e) => return Err(e) };
let v1640 = match s.builtin_core(EvalOp::Add, &[v1486, v1639]) { Ok(v) => v, Err(e) => return Err(e) };
let v1641 = match s.apply(v1484, v1640) { Ok(v) => v, Err(e) => return Err(e) };
let v1642 = match s.apply(v1468, v1641) { Ok(v) => v, Err(e) => return Err(e) };
let v1643 = match s.apply(v1467, v1642) { Ok(v) => v, Err(e) => return Err(e) };
let v1644 = match s.apply(v1463, v1643) { Ok(v) => v, Err(e) => return Err(e) };
let v1645 = match s.apply(v1285, v1644) { Ok(v) => v, Err(e) => return Err(e) };
let v1646 = match s.apply(v1284, v1645) { Ok(v) => v, Err(e) => return Err(e) };
let v1647 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1648 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1649 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1656 = match if_136_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1657 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1658 = match s.literal(Lit::Numeral(v1657)) { Ok(v) => v, Err(e) => return Err(e) };
let v1659 = match s.builtin_list(EvalOp::ListNth, &[v1649, v1656, v1658]) { Ok(v) => v, Err(e) => return Err(e) };
let v1660 = match s.apply(v1648, v1659) { Ok(v) => v, Err(e) => return Err(e) };
let v1661 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1662 = match s.literal(Lit::Numeral(v1661)) { Ok(v) => v, Err(e) => return Err(e) };
let v1663 = match s.apply(v1660, v1662) { Ok(v) => v, Err(e) => return Err(e) };
let v1664 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1665 = match s.literal(Lit::Numeral(v1664)) { Ok(v) => v, Err(e) => return Err(e) };
let v1786 = match if_147_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_153_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7, v1786, v1665, v1663, v1647, v1646, v1283)
}
pub(super) fn more_151_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v1290: Term, v1297: Term, v1289: Term, a0: Term, v4: Term, v7: Term, v1288: Term, v1287: Term, v24: Term, v1285: Term, v1284: Term, v1283: Term) -> CheckResult<Term> {
let v1298 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1299 = match s.literal(Lit::Numeral(v1298)) { Ok(v) => v, Err(e) => return Err(e) };
let v1300 = match s.builtin_list(EvalOp::ListNth, &[v1290, v1297, v1299]) { Ok(v) => v, Err(e) => return Err(e) };
let v1301 = match s.apply(v1289, v1300) { Ok(v) => v, Err(e) => return Err(e) };
let v1302 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1303 = match s.literal(Lit::Numeral(v1302)) { Ok(v) => v, Err(e) => return Err(e) };
let v1304 = match s.apply(v1301, v1303) { Ok(v) => v, Err(e) => return Err(e) };
let v1305 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1306 = match s.literal(Lit::Numeral(v1305)) { Ok(v) => v, Err(e) => return Err(e) };
let v1427 = match if_117_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1458 = match if_120_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1459 = match eo__24str_5foverlap_5frec(s, v1427, v1458) { Ok(v) => v, Err(e) => return Err(e) };
let v1460 = match s.builtin_core(EvalOp::Add, &[v1306, v1459]) { Ok(v) => v, Err(e) => return Err(e) };
let v1461 = match s.apply(v1304, v1460) { Ok(v) => v, Err(e) => return Err(e) };
let v1462 = match s.apply(v1288, v1461) { Ok(v) => v, Err(e) => return Err(e) };
let v1463 = match s.apply(v1287, v1462) { Ok(v) => v, Err(e) => return Err(e) };
let v1464 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1465 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1466 = match s.apply(v1465, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1467 = match s.apply(v1464, v1466) { Ok(v) => v, Err(e) => return Err(e) };
let v1468 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1469 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1470 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1477 = match if_121_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1478 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1479 = match s.literal(Lit::Numeral(v1478)) { Ok(v) => v, Err(e) => return Err(e) };
let v1480 = match s.builtin_list(EvalOp::ListNth, &[v1470, v1477, v1479]) { Ok(v) => v, Err(e) => return Err(e) };
let v1481 = match s.apply(v1469, v1480) { Ok(v) => v, Err(e) => return Err(e) };
more_152_eo__24eo_5fprog_5fconcat_5fcprop(s, v1481, a0, v4, v7, v1468, v1467, v1463, v1285, v1284, v1283)
}
pub(super) fn if_3_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v86 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v87, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.builtin_list(EvalOp::ListRev, &[v86, v88]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v89)
}
Some(false) => {
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v90, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v91)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v99 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v100, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListRev, &[v99, v101]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v102)
}
Some(false) => {
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v103, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v104)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v115 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v116, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.builtin_list(EvalOp::ListRev, &[v115, v117]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v118)
}
Some(false) => {
let v119 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v119, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v120)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v128 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v129, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_list(EvalOp::ListRev, &[v128, v130]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v131)
}
Some(false) => {
let v132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v132, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v133)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match if_3_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(v93)) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_list(EvalOp::ListNth, &[v85, v92, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(v96)) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match if_4_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(v106)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListNth, &[v98, v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_core(EvalOp::Length, &[v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Numeral(v110)) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_core(EvalOp::Add, &[v109, v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.builtin_core(EvalOp::Extract, &[v95, v97, v112]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
Some(false) => {
let v114 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match if_5_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_list(EvalOp::ListNth, &[v114, v121, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(v125)) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match if_6_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.literal(Lit::Numeral(v135)) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListNth, &[v127, v134, v136]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.builtin_core(EvalOp::Length, &[v137]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_core(EvalOp::Extract, &[v124, v126, v138]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v139)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v146 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v147, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.builtin_list(EvalOp::ListRev, &[v146, v148]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v149)
}
Some(false) => {
let v150 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v150, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v151)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v160, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListRev, &[v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v162)
}
Some(false) => {
let v163 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v163, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v164)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v175 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v176, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.builtin_list(EvalOp::ListRev, &[v175, v177]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v178)
}
Some(false) => {
let v179 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v179, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v180)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v189, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.builtin_list(EvalOp::ListRev, &[v188, v190]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v191)
}
Some(false) => {
let v192 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v192, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v193)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match if_8_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.literal(Lit::Numeral(v153)) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_list(EvalOp::ListNth, &[v145, v152, v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(v156)) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match if_9_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(v166)) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.builtin_list(EvalOp::ListNth, &[v158, v165, v167]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.builtin_core(EvalOp::Length, &[v168]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.literal(Lit::Numeral(v170)) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.builtin_core(EvalOp::Add, &[v169, v171]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_core(EvalOp::Extract, &[v155, v157, v172]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v173)
}
Some(false) => {
let v174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match if_10_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Numeral(v182)) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.builtin_list(EvalOp::ListNth, &[v174, v181, v183]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Numeral(v185)) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match if_11_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Numeral(v195)) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_list(EvalOp::ListNth, &[v187, v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.builtin_core(EvalOp::Length, &[v197]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.builtin_core(EvalOp::Extract, &[v184, v186, v198]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v199)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_13_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v83 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match if_7_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v84, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24str_5fflatten(s, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.builtin_list(EvalOp::ListRev, &[v83, v142]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v143)
}
Some(false) => {
let v144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match if_12_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v144, v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match eo__24str_5fflatten(s, v201) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v202)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v207 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v208, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.builtin_list(EvalOp::ListRev, &[v207, v209]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v210)
}
Some(false) => {
let v211 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v211, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v212)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v222 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v223, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.builtin_list(EvalOp::ListRev, &[v222, v224]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v225)
}
Some(false) => {
let v226 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v226, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v227)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_16_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v204 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match if_14_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Numeral(v214)) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.builtin_list(EvalOp::ListNth, &[v206, v213, v215]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v205, v216]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match eo__24str_5fflatten(s, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_list(EvalOp::ListRev, &[v204, v218]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v219)
}
Some(false) => {
let v220 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match if_15_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.builtin_list(EvalOp::ListNth, &[v221, v228, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v220, v231]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match eo__24str_5fflatten(s, v232) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v233)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_17_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v244 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v245, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.builtin_list(EvalOp::ListRev, &[v244, v246]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v247)
}
Some(false) => {
let v248 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v248, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v249)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_18_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v257 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v258, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_list(EvalOp::ListRev, &[v257, v259]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v260)
}
Some(false) => {
let v261 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v261, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v262)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_19_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v273 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v274, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.builtin_list(EvalOp::ListRev, &[v273, v275]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v276)
}
Some(false) => {
let v277 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v277, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v278)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_20_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v286 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v287, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.builtin_list(EvalOp::ListRev, &[v286, v288]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v289)
}
Some(false) => {
let v290 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v290, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v291)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v243 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match if_17_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.literal(Lit::Numeral(v251)) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.builtin_list(EvalOp::ListNth, &[v243, v250, v252]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Numeral(v254)) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match if_18_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.literal(Lit::Numeral(v264)) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.builtin_list(EvalOp::ListNth, &[v256, v263, v265]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.builtin_core(EvalOp::Length, &[v266]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.literal(Lit::Numeral(v268)) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.builtin_core(EvalOp::Add, &[v267, v269]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.builtin_core(EvalOp::Extract, &[v253, v255, v270]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v271)
}
Some(false) => {
let v272 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match if_19_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::Numeral(v280)) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.builtin_list(EvalOp::ListNth, &[v272, v279, v281]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.literal(Lit::Numeral(v283)) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match if_20_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.literal(Lit::Numeral(v293)) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.builtin_list(EvalOp::ListNth, &[v285, v292, v294]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.builtin_core(EvalOp::Length, &[v295]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.builtin_core(EvalOp::Extract, &[v282, v284, v296]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v297)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_22_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v304 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v305, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.builtin_list(EvalOp::ListRev, &[v304, v306]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v307)
}
Some(false) => {
let v308 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v308, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v309)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_23_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v317 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v318, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.builtin_list(EvalOp::ListRev, &[v317, v319]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v320)
}
Some(false) => {
let v321 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v321, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v322)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_24_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v333 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v334, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.builtin_list(EvalOp::ListRev, &[v333, v335]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v336)
}
Some(false) => {
let v337 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v337, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v338)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_25_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v346 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v347, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.builtin_list(EvalOp::ListRev, &[v346, v348]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v349)
}
Some(false) => {
let v350 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v350, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v351)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_26_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v303 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match if_22_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.literal(Lit::Numeral(v311)) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.builtin_list(EvalOp::ListNth, &[v303, v310, v312]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.literal(Lit::Numeral(v314)) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match if_23_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.literal(Lit::Numeral(v324)) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.builtin_list(EvalOp::ListNth, &[v316, v323, v325]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.builtin_core(EvalOp::Length, &[v326]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.literal(Lit::Numeral(v328)) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.builtin_core(EvalOp::Add, &[v327, v329]) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.builtin_core(EvalOp::Extract, &[v313, v315, v330]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v331)
}
Some(false) => {
let v332 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match if_24_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.literal(Lit::Numeral(v340)) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.builtin_list(EvalOp::ListNth, &[v332, v339, v341]) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.literal(Lit::Numeral(v343)) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match if_25_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.literal(Lit::Numeral(v353)) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.builtin_list(EvalOp::ListNth, &[v345, v352, v354]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.builtin_core(EvalOp::Length, &[v355]) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.builtin_core(EvalOp::Extract, &[v342, v344, v356]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v357)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_27_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v241 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match if_21_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v242, v298]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match eo__24str_5fflatten(s, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.builtin_list(EvalOp::ListRev, &[v241, v300]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v301)
}
Some(false) => {
let v302 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match if_26_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v302, v358]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match eo__24str_5fflatten(s, v359) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v360)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_28_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v365 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v366, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.builtin_list(EvalOp::ListRev, &[v365, v367]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v368)
}
Some(false) => {
let v369 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v369, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v370)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_29_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v380 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v381, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_list(EvalOp::ListRev, &[v380, v382]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v383)
}
Some(false) => {
let v384 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v384, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v385)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_30_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v362 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match if_28_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.literal(Lit::Numeral(v372)) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.builtin_list(EvalOp::ListNth, &[v364, v371, v373]) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v363, v374]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match eo__24str_5fflatten(s, v375) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.builtin_list(EvalOp::ListRev, &[v362, v376]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v377)
}
Some(false) => {
let v378 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match if_29_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.literal(Lit::Numeral(v387)) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.builtin_list(EvalOp::ListNth, &[v379, v386, v388]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v378, v389]) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match eo__24str_5fflatten(s, v390) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v391)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_31_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v404 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v405, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.builtin_list(EvalOp::ListRev, &[v404, v406]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v407)
}
Some(false) => {
let v408 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v408, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v409)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_32_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v418 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v419, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.builtin_list(EvalOp::ListRev, &[v418, v420]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v421)
}
Some(false) => {
let v422 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v422, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v423)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_33_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v435 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v436, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.builtin_list(EvalOp::ListRev, &[v435, v437]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v438)
}
Some(false) => {
let v439 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v439, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v440)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_34_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v448 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v449, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.builtin_list(EvalOp::ListRev, &[v448, v450]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v451)
}
Some(false) => {
let v452 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v452, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v453)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_35_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v464 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v465, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.builtin_list(EvalOp::ListRev, &[v464, v466]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v467)
}
Some(false) => {
let v468 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v468, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v469)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_36_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v477 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v478, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.builtin_list(EvalOp::ListRev, &[v477, v479]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v480)
}
Some(false) => {
let v481 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v482 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v481, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v482)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_37_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v434 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match if_33_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.literal(Lit::Numeral(v442)) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.builtin_list(EvalOp::ListNth, &[v434, v441, v443]) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.literal(Lit::Numeral(v445)) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match if_34_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.literal(Lit::Numeral(v455)) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.builtin_list(EvalOp::ListNth, &[v447, v454, v456]) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.builtin_core(EvalOp::Length, &[v457]) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.literal(Lit::Numeral(v459)) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.builtin_core(EvalOp::Add, &[v458, v460]) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.builtin_core(EvalOp::Extract, &[v444, v446, v461]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v462)
}
Some(false) => {
let v463 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match if_35_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match s.literal(Lit::Numeral(v471)) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.builtin_list(EvalOp::ListNth, &[v463, v470, v472]) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v475 = match s.literal(Lit::Numeral(v474)) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match if_36_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match s.literal(Lit::Numeral(v484)) { Ok(v) => v, Err(e) => return Err(e) };
let v486 = match s.builtin_list(EvalOp::ListNth, &[v476, v483, v485]) { Ok(v) => v, Err(e) => return Err(e) };
let v487 = match s.builtin_core(EvalOp::Length, &[v486]) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match s.builtin_core(EvalOp::Extract, &[v473, v475, v487]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v488)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_38_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v495 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v497 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v496, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match s.builtin_list(EvalOp::ListRev, &[v495, v497]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v498)
}
Some(false) => {
let v499 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v500 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v499, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v500)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_39_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v508 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v509, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v511 = match s.builtin_list(EvalOp::ListRev, &[v508, v510]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v511)
}
Some(false) => {
let v512 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v512, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v513)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_40_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v524 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v525 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v526 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v525, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v527 = match s.builtin_list(EvalOp::ListRev, &[v524, v526]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v527)
}
Some(false) => {
let v528 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v529 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v528, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v529)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_41_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v537 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v538 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v539 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v538, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v540 = match s.builtin_list(EvalOp::ListRev, &[v537, v539]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v540)
}
Some(false) => {
let v541 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v542 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v541, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v542)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_42_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v494 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match if_38_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v503 = match s.literal(Lit::Numeral(v502)) { Ok(v) => v, Err(e) => return Err(e) };
let v504 = match s.builtin_list(EvalOp::ListNth, &[v494, v501, v503]) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match s.literal(Lit::Numeral(v505)) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v514 = match if_39_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v515 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v516 = match s.literal(Lit::Numeral(v515)) { Ok(v) => v, Err(e) => return Err(e) };
let v517 = match s.builtin_list(EvalOp::ListNth, &[v507, v514, v516]) { Ok(v) => v, Err(e) => return Err(e) };
let v518 = match s.builtin_core(EvalOp::Length, &[v517]) { Ok(v) => v, Err(e) => return Err(e) };
let v519 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v520 = match s.literal(Lit::Numeral(v519)) { Ok(v) => v, Err(e) => return Err(e) };
let v521 = match s.builtin_core(EvalOp::Add, &[v518, v520]) { Ok(v) => v, Err(e) => return Err(e) };
let v522 = match s.builtin_core(EvalOp::Extract, &[v504, v506, v521]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v522)
}
Some(false) => {
let v523 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v530 = match if_40_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v531 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v532 = match s.literal(Lit::Numeral(v531)) { Ok(v) => v, Err(e) => return Err(e) };
let v533 = match s.builtin_list(EvalOp::ListNth, &[v523, v530, v532]) { Ok(v) => v, Err(e) => return Err(e) };
let v534 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v535 = match s.literal(Lit::Numeral(v534)) { Ok(v) => v, Err(e) => return Err(e) };
let v536 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v543 = match if_41_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v544 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v545 = match s.literal(Lit::Numeral(v544)) { Ok(v) => v, Err(e) => return Err(e) };
let v546 = match s.builtin_list(EvalOp::ListNth, &[v536, v543, v545]) { Ok(v) => v, Err(e) => return Err(e) };
let v547 = match s.builtin_core(EvalOp::Length, &[v546]) { Ok(v) => v, Err(e) => return Err(e) };
let v548 = match s.builtin_core(EvalOp::Extract, &[v533, v535, v547]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v548)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_43_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v432 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match if_37_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v433, v489]) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match eo__24str_5fflatten(s, v490) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match s.builtin_list(EvalOp::ListRev, &[v432, v491]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v492)
}
Some(false) => {
let v493 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v549 = match if_42_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v550 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v493, v549]) { Ok(v) => v, Err(e) => return Err(e) };
let v551 = match eo__24str_5fflatten(s, v550) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v551)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_44_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v556 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v557 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v558 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v557, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v559 = match s.builtin_list(EvalOp::ListRev, &[v556, v558]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v559)
}
Some(false) => {
let v560 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v561 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v560, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v561)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_45_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v571 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v572 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v573 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v572, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v574 = match s.builtin_list(EvalOp::ListRev, &[v571, v573]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v574)
}
Some(false) => {
let v575 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v576 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v575, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v576)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_46_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v553 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v554 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v555 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v562 = match if_44_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v563 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v564 = match s.literal(Lit::Numeral(v563)) { Ok(v) => v, Err(e) => return Err(e) };
let v565 = match s.builtin_list(EvalOp::ListNth, &[v555, v562, v564]) { Ok(v) => v, Err(e) => return Err(e) };
let v566 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v554, v565]) { Ok(v) => v, Err(e) => return Err(e) };
let v567 = match eo__24str_5fflatten(s, v566) { Ok(v) => v, Err(e) => return Err(e) };
let v568 = match s.builtin_list(EvalOp::ListRev, &[v553, v567]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v568)
}
Some(false) => {
let v569 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v570 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v577 = match if_45_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v578 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v579 = match s.literal(Lit::Numeral(v578)) { Ok(v) => v, Err(e) => return Err(e) };
let v580 = match s.builtin_list(EvalOp::ListNth, &[v570, v577, v579]) { Ok(v) => v, Err(e) => return Err(e) };
let v581 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v569, v580]) { Ok(v) => v, Err(e) => return Err(e) };
let v582 = match eo__24str_5fflatten(s, v581) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v582)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_47_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v593 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v594 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v595 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v594, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v596 = match s.builtin_list(EvalOp::ListRev, &[v593, v595]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v596)
}
Some(false) => {
let v597 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v598 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v597, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v598)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_48_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v606 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v607 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v608 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v607, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v609 = match s.builtin_list(EvalOp::ListRev, &[v606, v608]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v609)
}
Some(false) => {
let v610 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v611 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v610, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v611)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_49_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v622 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v623 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v624 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v623, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v625 = match s.builtin_list(EvalOp::ListRev, &[v622, v624]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v625)
}
Some(false) => {
let v626 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v627 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v626, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v627)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_50_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v635 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v636 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v637 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v636, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v638 = match s.builtin_list(EvalOp::ListRev, &[v635, v637]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v638)
}
Some(false) => {
let v639 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v640 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v639, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v640)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_51_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v592 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v599 = match if_47_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v600 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v601 = match s.literal(Lit::Numeral(v600)) { Ok(v) => v, Err(e) => return Err(e) };
let v602 = match s.builtin_list(EvalOp::ListNth, &[v592, v599, v601]) { Ok(v) => v, Err(e) => return Err(e) };
let v603 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v604 = match s.literal(Lit::Numeral(v603)) { Ok(v) => v, Err(e) => return Err(e) };
let v605 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v612 = match if_48_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v613 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v614 = match s.literal(Lit::Numeral(v613)) { Ok(v) => v, Err(e) => return Err(e) };
let v615 = match s.builtin_list(EvalOp::ListNth, &[v605, v612, v614]) { Ok(v) => v, Err(e) => return Err(e) };
let v616 = match s.builtin_core(EvalOp::Length, &[v615]) { Ok(v) => v, Err(e) => return Err(e) };
let v617 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v618 = match s.literal(Lit::Numeral(v617)) { Ok(v) => v, Err(e) => return Err(e) };
let v619 = match s.builtin_core(EvalOp::Add, &[v616, v618]) { Ok(v) => v, Err(e) => return Err(e) };
let v620 = match s.builtin_core(EvalOp::Extract, &[v602, v604, v619]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v620)
}
Some(false) => {
let v621 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v628 = match if_49_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v629 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v630 = match s.literal(Lit::Numeral(v629)) { Ok(v) => v, Err(e) => return Err(e) };
let v631 = match s.builtin_list(EvalOp::ListNth, &[v621, v628, v630]) { Ok(v) => v, Err(e) => return Err(e) };
let v632 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v633 = match s.literal(Lit::Numeral(v632)) { Ok(v) => v, Err(e) => return Err(e) };
let v634 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v641 = match if_50_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v642 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v643 = match s.literal(Lit::Numeral(v642)) { Ok(v) => v, Err(e) => return Err(e) };
let v644 = match s.builtin_list(EvalOp::ListNth, &[v634, v641, v643]) { Ok(v) => v, Err(e) => return Err(e) };
let v645 = match s.builtin_core(EvalOp::Length, &[v644]) { Ok(v) => v, Err(e) => return Err(e) };
let v646 = match s.builtin_core(EvalOp::Extract, &[v631, v633, v645]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v646)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_52_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v653 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v654 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v655 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v654, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v656 = match s.builtin_list(EvalOp::ListRev, &[v653, v655]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v656)
}
Some(false) => {
let v657 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v658 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v657, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v658)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_53_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v666 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v667 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v668 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v667, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v669 = match s.builtin_list(EvalOp::ListRev, &[v666, v668]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v669)
}
Some(false) => {
let v670 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v671 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v670, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v671)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_54_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v682 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v683 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v684 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v683, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v685 = match s.builtin_list(EvalOp::ListRev, &[v682, v684]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v685)
}
Some(false) => {
let v686 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v687 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v686, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v687)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_55_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v695 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v696 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v697 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v696, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v698 = match s.builtin_list(EvalOp::ListRev, &[v695, v697]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v698)
}
Some(false) => {
let v699 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v700 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v699, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v700)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_56_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v652 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v659 = match if_52_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v660 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v661 = match s.literal(Lit::Numeral(v660)) { Ok(v) => v, Err(e) => return Err(e) };
let v662 = match s.builtin_list(EvalOp::ListNth, &[v652, v659, v661]) { Ok(v) => v, Err(e) => return Err(e) };
let v663 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v664 = match s.literal(Lit::Numeral(v663)) { Ok(v) => v, Err(e) => return Err(e) };
let v665 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v672 = match if_53_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v673 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v674 = match s.literal(Lit::Numeral(v673)) { Ok(v) => v, Err(e) => return Err(e) };
let v675 = match s.builtin_list(EvalOp::ListNth, &[v665, v672, v674]) { Ok(v) => v, Err(e) => return Err(e) };
let v676 = match s.builtin_core(EvalOp::Length, &[v675]) { Ok(v) => v, Err(e) => return Err(e) };
let v677 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v678 = match s.literal(Lit::Numeral(v677)) { Ok(v) => v, Err(e) => return Err(e) };
let v679 = match s.builtin_core(EvalOp::Add, &[v676, v678]) { Ok(v) => v, Err(e) => return Err(e) };
let v680 = match s.builtin_core(EvalOp::Extract, &[v662, v664, v679]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v680)
}
Some(false) => {
let v681 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v688 = match if_54_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v689 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v690 = match s.literal(Lit::Numeral(v689)) { Ok(v) => v, Err(e) => return Err(e) };
let v691 = match s.builtin_list(EvalOp::ListNth, &[v681, v688, v690]) { Ok(v) => v, Err(e) => return Err(e) };
let v692 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v693 = match s.literal(Lit::Numeral(v692)) { Ok(v) => v, Err(e) => return Err(e) };
let v694 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v701 = match if_55_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v702 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v703 = match s.literal(Lit::Numeral(v702)) { Ok(v) => v, Err(e) => return Err(e) };
let v704 = match s.builtin_list(EvalOp::ListNth, &[v694, v701, v703]) { Ok(v) => v, Err(e) => return Err(e) };
let v705 = match s.builtin_core(EvalOp::Length, &[v704]) { Ok(v) => v, Err(e) => return Err(e) };
let v706 = match s.builtin_core(EvalOp::Extract, &[v691, v693, v705]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v706)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_57_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v590 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v591 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v647 = match if_51_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v648 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v591, v647]) { Ok(v) => v, Err(e) => return Err(e) };
let v649 = match eo__24str_5fflatten(s, v648) { Ok(v) => v, Err(e) => return Err(e) };
let v650 = match s.builtin_list(EvalOp::ListRev, &[v590, v649]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v650)
}
Some(false) => {
let v651 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v707 = match if_56_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v708 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v651, v707]) { Ok(v) => v, Err(e) => return Err(e) };
let v709 = match eo__24str_5fflatten(s, v708) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v709)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_58_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v714 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v715 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v716 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v715, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v717 = match s.builtin_list(EvalOp::ListRev, &[v714, v716]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v717)
}
Some(false) => {
let v718 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v719 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v718, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v719)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_59_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v729 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v730 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v731 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v730, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v732 = match s.builtin_list(EvalOp::ListRev, &[v729, v731]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v732)
}
Some(false) => {
let v733 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v734 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v733, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v734)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_60_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v711 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v712 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v713 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v720 = match if_58_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v721 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v722 = match s.literal(Lit::Numeral(v721)) { Ok(v) => v, Err(e) => return Err(e) };
let v723 = match s.builtin_list(EvalOp::ListNth, &[v713, v720, v722]) { Ok(v) => v, Err(e) => return Err(e) };
let v724 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v712, v723]) { Ok(v) => v, Err(e) => return Err(e) };
let v725 = match eo__24str_5fflatten(s, v724) { Ok(v) => v, Err(e) => return Err(e) };
let v726 = match s.builtin_list(EvalOp::ListRev, &[v711, v725]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v726)
}
Some(false) => {
let v727 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v728 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v735 = match if_59_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v736 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v737 = match s.literal(Lit::Numeral(v736)) { Ok(v) => v, Err(e) => return Err(e) };
let v738 = match s.builtin_list(EvalOp::ListNth, &[v728, v735, v737]) { Ok(v) => v, Err(e) => return Err(e) };
let v739 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v727, v738]) { Ok(v) => v, Err(e) => return Err(e) };
let v740 = match eo__24str_5fflatten(s, v739) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v740)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_61_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v760 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v761 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v762 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v761, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v763 = match s.builtin_list(EvalOp::ListRev, &[v760, v762]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v763)
}
Some(false) => {
let v764 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v765 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v764, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v765)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_62_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v774 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v775 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v776 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v775, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v777 = match s.builtin_list(EvalOp::ListRev, &[v774, v776]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v777)
}
Some(false) => {
let v778 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v779 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v778, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v779)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_63_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v791 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v792 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v793 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v792, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v794 = match s.builtin_list(EvalOp::ListRev, &[v791, v793]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v794)
}
Some(false) => {
let v795 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v796 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v795, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v796)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_64_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v804 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v805 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v806 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v805, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v807 = match s.builtin_list(EvalOp::ListRev, &[v804, v806]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v807)
}
Some(false) => {
let v808 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v809 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v808, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v809)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_65_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v820 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v821 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v822 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v821, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v823 = match s.builtin_list(EvalOp::ListRev, &[v820, v822]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v823)
}
Some(false) => {
let v824 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v825 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v824, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v825)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_66_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v833 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v834 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v835 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v834, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v836 = match s.builtin_list(EvalOp::ListRev, &[v833, v835]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v836)
}
Some(false) => {
let v837 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v838 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v837, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v838)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_67_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v790 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v797 = match if_63_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v798 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v799 = match s.literal(Lit::Numeral(v798)) { Ok(v) => v, Err(e) => return Err(e) };
let v800 = match s.builtin_list(EvalOp::ListNth, &[v790, v797, v799]) { Ok(v) => v, Err(e) => return Err(e) };
let v801 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v802 = match s.literal(Lit::Numeral(v801)) { Ok(v) => v, Err(e) => return Err(e) };
let v803 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v810 = match if_64_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v811 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v812 = match s.literal(Lit::Numeral(v811)) { Ok(v) => v, Err(e) => return Err(e) };
let v813 = match s.builtin_list(EvalOp::ListNth, &[v803, v810, v812]) { Ok(v) => v, Err(e) => return Err(e) };
let v814 = match s.builtin_core(EvalOp::Length, &[v813]) { Ok(v) => v, Err(e) => return Err(e) };
let v815 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v816 = match s.literal(Lit::Numeral(v815)) { Ok(v) => v, Err(e) => return Err(e) };
let v817 = match s.builtin_core(EvalOp::Add, &[v814, v816]) { Ok(v) => v, Err(e) => return Err(e) };
let v818 = match s.builtin_core(EvalOp::Extract, &[v800, v802, v817]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v818)
}
Some(false) => {
let v819 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v826 = match if_65_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v827 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v828 = match s.literal(Lit::Numeral(v827)) { Ok(v) => v, Err(e) => return Err(e) };
let v829 = match s.builtin_list(EvalOp::ListNth, &[v819, v826, v828]) { Ok(v) => v, Err(e) => return Err(e) };
let v830 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v831 = match s.literal(Lit::Numeral(v830)) { Ok(v) => v, Err(e) => return Err(e) };
let v832 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v839 = match if_66_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v840 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v841 = match s.literal(Lit::Numeral(v840)) { Ok(v) => v, Err(e) => return Err(e) };
let v842 = match s.builtin_list(EvalOp::ListNth, &[v832, v839, v841]) { Ok(v) => v, Err(e) => return Err(e) };
let v843 = match s.builtin_core(EvalOp::Length, &[v842]) { Ok(v) => v, Err(e) => return Err(e) };
let v844 = match s.builtin_core(EvalOp::Extract, &[v829, v831, v843]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v844)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_68_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v851 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v852 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v853 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v852, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v854 = match s.builtin_list(EvalOp::ListRev, &[v851, v853]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v854)
}
Some(false) => {
let v855 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v856 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v855, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v856)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_69_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v864 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v865 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v866 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v865, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v867 = match s.builtin_list(EvalOp::ListRev, &[v864, v866]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v867)
}
Some(false) => {
let v868 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v869 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v868, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v869)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_70_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v880 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v881 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v882 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v881, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v883 = match s.builtin_list(EvalOp::ListRev, &[v880, v882]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v883)
}
Some(false) => {
let v884 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v885 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v884, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v885)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_71_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v893 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v894 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v895 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v894, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v896 = match s.builtin_list(EvalOp::ListRev, &[v893, v895]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v896)
}
Some(false) => {
let v897 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v898 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v897, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v898)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_72_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v850 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v857 = match if_68_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v858 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v859 = match s.literal(Lit::Numeral(v858)) { Ok(v) => v, Err(e) => return Err(e) };
let v860 = match s.builtin_list(EvalOp::ListNth, &[v850, v857, v859]) { Ok(v) => v, Err(e) => return Err(e) };
let v861 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v862 = match s.literal(Lit::Numeral(v861)) { Ok(v) => v, Err(e) => return Err(e) };
let v863 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v870 = match if_69_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v871 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v872 = match s.literal(Lit::Numeral(v871)) { Ok(v) => v, Err(e) => return Err(e) };
let v873 = match s.builtin_list(EvalOp::ListNth, &[v863, v870, v872]) { Ok(v) => v, Err(e) => return Err(e) };
let v874 = match s.builtin_core(EvalOp::Length, &[v873]) { Ok(v) => v, Err(e) => return Err(e) };
let v875 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v876 = match s.literal(Lit::Numeral(v875)) { Ok(v) => v, Err(e) => return Err(e) };
let v877 = match s.builtin_core(EvalOp::Add, &[v874, v876]) { Ok(v) => v, Err(e) => return Err(e) };
let v878 = match s.builtin_core(EvalOp::Extract, &[v860, v862, v877]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v878)
}
Some(false) => {
let v879 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v886 = match if_70_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v887 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v888 = match s.literal(Lit::Numeral(v887)) { Ok(v) => v, Err(e) => return Err(e) };
let v889 = match s.builtin_list(EvalOp::ListNth, &[v879, v886, v888]) { Ok(v) => v, Err(e) => return Err(e) };
let v890 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v891 = match s.literal(Lit::Numeral(v890)) { Ok(v) => v, Err(e) => return Err(e) };
let v892 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v899 = match if_71_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v900 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v901 = match s.literal(Lit::Numeral(v900)) { Ok(v) => v, Err(e) => return Err(e) };
let v902 = match s.builtin_list(EvalOp::ListNth, &[v892, v899, v901]) { Ok(v) => v, Err(e) => return Err(e) };
let v903 = match s.builtin_core(EvalOp::Length, &[v902]) { Ok(v) => v, Err(e) => return Err(e) };
let v904 = match s.builtin_core(EvalOp::Extract, &[v889, v891, v903]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v904)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_73_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v788 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v789 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v845 = match if_67_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v846 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v789, v845]) { Ok(v) => v, Err(e) => return Err(e) };
let v847 = match eo__24str_5fflatten(s, v846) { Ok(v) => v, Err(e) => return Err(e) };
let v848 = match s.builtin_list(EvalOp::ListRev, &[v788, v847]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v848)
}
Some(false) => {
let v849 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v905 = match if_72_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v906 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v849, v905]) { Ok(v) => v, Err(e) => return Err(e) };
let v907 = match eo__24str_5fflatten(s, v906) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v907)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_74_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v912 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v913 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v914 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v913, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v915 = match s.builtin_list(EvalOp::ListRev, &[v912, v914]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v915)
}
Some(false) => {
let v916 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v917 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v916, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v917)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_75_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v927 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v928 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v929 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v928, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v930 = match s.builtin_list(EvalOp::ListRev, &[v927, v929]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v930)
}
Some(false) => {
let v931 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v932 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v931, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v932)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_76_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v909 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v910 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v911 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v918 = match if_74_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v919 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v920 = match s.literal(Lit::Numeral(v919)) { Ok(v) => v, Err(e) => return Err(e) };
let v921 = match s.builtin_list(EvalOp::ListNth, &[v911, v918, v920]) { Ok(v) => v, Err(e) => return Err(e) };
let v922 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v910, v921]) { Ok(v) => v, Err(e) => return Err(e) };
let v923 = match eo__24str_5fflatten(s, v922) { Ok(v) => v, Err(e) => return Err(e) };
let v924 = match s.builtin_list(EvalOp::ListRev, &[v909, v923]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v924)
}
Some(false) => {
let v925 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v926 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v933 = match if_75_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v934 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v935 = match s.literal(Lit::Numeral(v934)) { Ok(v) => v, Err(e) => return Err(e) };
let v936 = match s.builtin_list(EvalOp::ListNth, &[v926, v933, v935]) { Ok(v) => v, Err(e) => return Err(e) };
let v937 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v925, v936]) { Ok(v) => v, Err(e) => return Err(e) };
let v938 = match eo__24str_5fflatten(s, v937) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v938)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_77_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v949 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v950 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v951 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v950, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v952 = match s.builtin_list(EvalOp::ListRev, &[v949, v951]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v952)
}
Some(false) => {
let v953 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v954 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v953, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v954)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_78_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v962 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v963 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v964 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v963, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v965 = match s.builtin_list(EvalOp::ListRev, &[v962, v964]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v965)
}
Some(false) => {
let v966 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v967 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v966, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v967)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_79_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v978 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v979 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v980 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v979, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v981 = match s.builtin_list(EvalOp::ListRev, &[v978, v980]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v981)
}
Some(false) => {
let v982 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v983 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v982, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v983)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_80_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v991 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v992 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v993 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v992, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v994 = match s.builtin_list(EvalOp::ListRev, &[v991, v993]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v994)
}
Some(false) => {
let v995 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v996 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v995, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v996)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_81_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v948 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v955 = match if_77_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v956 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v957 = match s.literal(Lit::Numeral(v956)) { Ok(v) => v, Err(e) => return Err(e) };
let v958 = match s.builtin_list(EvalOp::ListNth, &[v948, v955, v957]) { Ok(v) => v, Err(e) => return Err(e) };
let v959 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v960 = match s.literal(Lit::Numeral(v959)) { Ok(v) => v, Err(e) => return Err(e) };
let v961 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v968 = match if_78_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v969 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v970 = match s.literal(Lit::Numeral(v969)) { Ok(v) => v, Err(e) => return Err(e) };
let v971 = match s.builtin_list(EvalOp::ListNth, &[v961, v968, v970]) { Ok(v) => v, Err(e) => return Err(e) };
let v972 = match s.builtin_core(EvalOp::Length, &[v971]) { Ok(v) => v, Err(e) => return Err(e) };
let v973 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v974 = match s.literal(Lit::Numeral(v973)) { Ok(v) => v, Err(e) => return Err(e) };
let v975 = match s.builtin_core(EvalOp::Add, &[v972, v974]) { Ok(v) => v, Err(e) => return Err(e) };
let v976 = match s.builtin_core(EvalOp::Extract, &[v958, v960, v975]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v976)
}
Some(false) => {
let v977 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v984 = match if_79_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v985 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v986 = match s.literal(Lit::Numeral(v985)) { Ok(v) => v, Err(e) => return Err(e) };
let v987 = match s.builtin_list(EvalOp::ListNth, &[v977, v984, v986]) { Ok(v) => v, Err(e) => return Err(e) };
let v988 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v989 = match s.literal(Lit::Numeral(v988)) { Ok(v) => v, Err(e) => return Err(e) };
let v990 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v997 = match if_80_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v998 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v999 = match s.literal(Lit::Numeral(v998)) { Ok(v) => v, Err(e) => return Err(e) };
let v1000 = match s.builtin_list(EvalOp::ListNth, &[v990, v997, v999]) { Ok(v) => v, Err(e) => return Err(e) };
let v1001 = match s.builtin_core(EvalOp::Length, &[v1000]) { Ok(v) => v, Err(e) => return Err(e) };
let v1002 = match s.builtin_core(EvalOp::Extract, &[v987, v989, v1001]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1002)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_82_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1009 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1010 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1011 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1010, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1012 = match s.builtin_list(EvalOp::ListRev, &[v1009, v1011]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1012)
}
Some(false) => {
let v1013 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1014 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1013, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1014)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_83_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1022 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1023 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1024 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1023, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1025 = match s.builtin_list(EvalOp::ListRev, &[v1022, v1024]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1025)
}
Some(false) => {
let v1026 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1027 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1026, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1027)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_84_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1038 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1039 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1040 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1039, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1041 = match s.builtin_list(EvalOp::ListRev, &[v1038, v1040]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1041)
}
Some(false) => {
let v1042 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1043 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1042, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1043)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_85_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1051 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1052 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1053 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1052, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v1054 = match s.builtin_list(EvalOp::ListRev, &[v1051, v1053]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1054)
}
Some(false) => {
let v1055 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1056 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1055, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1056)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_86_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1008 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1015 = match if_82_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1016 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1017 = match s.literal(Lit::Numeral(v1016)) { Ok(v) => v, Err(e) => return Err(e) };
let v1018 = match s.builtin_list(EvalOp::ListNth, &[v1008, v1015, v1017]) { Ok(v) => v, Err(e) => return Err(e) };
let v1019 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1020 = match s.literal(Lit::Numeral(v1019)) { Ok(v) => v, Err(e) => return Err(e) };
let v1021 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1028 = match if_83_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1029 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1030 = match s.literal(Lit::Numeral(v1029)) { Ok(v) => v, Err(e) => return Err(e) };
let v1031 = match s.builtin_list(EvalOp::ListNth, &[v1021, v1028, v1030]) { Ok(v) => v, Err(e) => return Err(e) };
let v1032 = match s.builtin_core(EvalOp::Length, &[v1031]) { Ok(v) => v, Err(e) => return Err(e) };
let v1033 = match parse_int("-2") { Ok(v) => v, Err(e) => return Err(e) };
let v1034 = match s.literal(Lit::Numeral(v1033)) { Ok(v) => v, Err(e) => return Err(e) };
let v1035 = match s.builtin_core(EvalOp::Add, &[v1032, v1034]) { Ok(v) => v, Err(e) => return Err(e) };
let v1036 = match s.builtin_core(EvalOp::Extract, &[v1018, v1020, v1035]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1036)
}
Some(false) => {
let v1037 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1044 = match if_84_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1045 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1046 = match s.literal(Lit::Numeral(v1045)) { Ok(v) => v, Err(e) => return Err(e) };
let v1047 = match s.builtin_list(EvalOp::ListNth, &[v1037, v1044, v1046]) { Ok(v) => v, Err(e) => return Err(e) };
let v1048 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1049 = match s.literal(Lit::Numeral(v1048)) { Ok(v) => v, Err(e) => return Err(e) };
let v1050 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1057 = match if_85_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1058 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1059 = match s.literal(Lit::Numeral(v1058)) { Ok(v) => v, Err(e) => return Err(e) };
let v1060 = match s.builtin_list(EvalOp::ListNth, &[v1050, v1057, v1059]) { Ok(v) => v, Err(e) => return Err(e) };
let v1061 = match s.builtin_core(EvalOp::Length, &[v1060]) { Ok(v) => v, Err(e) => return Err(e) };
let v1062 = match s.builtin_core(EvalOp::Extract, &[v1047, v1049, v1061]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1062)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_87_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v946 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v947 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1003 = match if_81_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1004 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v947, v1003]) { Ok(v) => v, Err(e) => return Err(e) };
let v1005 = match eo__24str_5fflatten(s, v1004) { Ok(v) => v, Err(e) => return Err(e) };
let v1006 = match s.builtin_list(EvalOp::ListRev, &[v946, v1005]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1006)
}
Some(false) => {
let v1007 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1063 = match if_86_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1064 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1007, v1063]) { Ok(v) => v, Err(e) => return Err(e) };
let v1065 = match eo__24str_5fflatten(s, v1064) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1065)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_88_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1070 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1071 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1072 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1071, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1073 = match s.builtin_list(EvalOp::ListRev, &[v1070, v1072]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1073)
}
Some(false) => {
let v1074 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1075 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1074, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1075)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_89_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1085 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1086 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1087 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1086, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v1088 = match s.builtin_list(EvalOp::ListRev, &[v1085, v1087]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1088)
}
Some(false) => {
let v1089 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1090 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1089, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1090)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_90_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, a0: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1067 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1068 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1069 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1076 = match if_88_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1077 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1078 = match s.literal(Lit::Numeral(v1077)) { Ok(v) => v, Err(e) => return Err(e) };
let v1079 = match s.builtin_list(EvalOp::ListNth, &[v1069, v1076, v1078]) { Ok(v) => v, Err(e) => return Err(e) };
let v1080 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1068, v1079]) { Ok(v) => v, Err(e) => return Err(e) };
let v1081 = match eo__24str_5fflatten(s, v1080) { Ok(v) => v, Err(e) => return Err(e) };
let v1082 = match s.builtin_list(EvalOp::ListRev, &[v1067, v1081]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1082)
}
Some(false) => {
let v1083 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1084 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1091 = match if_89_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1092 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1093 = match s.literal(Lit::Numeral(v1092)) { Ok(v) => v, Err(e) => return Err(e) };
let v1094 = match s.builtin_list(EvalOp::ListNth, &[v1084, v1091, v1093]) { Ok(v) => v, Err(e) => return Err(e) };
let v1095 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1083, v1094]) { Ok(v) => v, Err(e) => return Err(e) };
let v1096 = match eo__24str_5fflatten(s, v1095) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1096)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_157_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v771: Term, v784: Term, a0: Term, v4: Term, v7: Term, v770: Term, v757: Term, v756: Term, v752: Term, v747: Term, v746: Term, v745: Term, v400: Term) -> CheckResult<Term> {
let v785 = match s.apply(v771, v784) { Ok(v) => v, Err(e) => return Err(e) };
let v786 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v787 = match s.literal(Lit::Numeral(v786)) { Ok(v) => v, Err(e) => return Err(e) };
let v908 = match if_73_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v939 = match if_76_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v940 = match eo__24str_5foverlap_5frec(s, v908, v939) { Ok(v) => v, Err(e) => return Err(e) };
let v941 = match s.builtin_core(EvalOp::Add, &[v787, v940]) { Ok(v) => v, Err(e) => return Err(e) };
let v942 = match s.apply(v785, v941) { Ok(v) => v, Err(e) => return Err(e) };
let v943 = match s.apply(v770, v942) { Ok(v) => v, Err(e) => return Err(e) };
let v944 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v945 = match s.literal(Lit::Numeral(v944)) { Ok(v) => v, Err(e) => return Err(e) };
let v1066 = match if_87_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1097 = match if_90_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1098 = match eo__24str_5foverlap_5frec(s, v1066, v1097) { Ok(v) => v, Err(e) => return Err(e) };
let v1099 = match s.builtin_core(EvalOp::Add, &[v945, v1098]) { Ok(v) => v, Err(e) => return Err(e) };
let v1100 = match s.apply(v943, v1099) { Ok(v) => v, Err(e) => return Err(e) };
let v1101 = match s.apply(v757, v1100) { Ok(v) => v, Err(e) => return Err(e) };
let v1102 = match s.apply(v756, v1101) { Ok(v) => v, Err(e) => return Err(e) };
let v1103 = match s.apply(v752, v1102) { Ok(v) => v, Err(e) => return Err(e) };
let v1104 = match s.apply(v747, v1103) { Ok(v) => v, Err(e) => return Err(e) };
let v1105 = match eo__24eo_5ftypeof(s, v1104) { Ok(v) => v, Err(e) => return Err(e) };
let v1106 = match eo__24eo_5fnil(s, v746, v1105) { Ok(v) => v, Err(e) => return Err(e) };
let v1107 = match s.apply(v745, v1106) { Ok(v) => v, Err(e) => return Err(e) };
let v1108 = match s.apply(v400, v1107) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1108)
}
pub(super) fn more_156_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v24: Term, a0: Term, v4: Term, v7: Term, v745: Term, v400: Term) -> CheckResult<Term> {
let v746 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v747 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v748 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v749 = match s.apply(v748, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v750 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v751 = match s.literal(Lit::Numeral(v750)) { Ok(v) => v, Err(e) => return Err(e) };
let v752 = match s.apply(v749, v751) { Ok(v) => v, Err(e) => return Err(e) };
let v753 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v754 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v755 = match s.apply(v754, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v756 = match s.apply(v753, v755) { Ok(v) => v, Err(e) => return Err(e) };
let v757 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v758 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v759 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v766 = match if_61_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v767 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v768 = match s.literal(Lit::Numeral(v767)) { Ok(v) => v, Err(e) => return Err(e) };
let v769 = match s.builtin_list(EvalOp::ListNth, &[v759, v766, v768]) { Ok(v) => v, Err(e) => return Err(e) };
let v770 = match s.apply(v758, v769) { Ok(v) => v, Err(e) => return Err(e) };
let v771 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v772 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v773 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v780 = match if_62_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v781 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v782 = match s.literal(Lit::Numeral(v781)) { Ok(v) => v, Err(e) => return Err(e) };
let v783 = match s.builtin_list(EvalOp::ListNth, &[v773, v780, v782]) { Ok(v) => v, Err(e) => return Err(e) };
let v784 = match s.apply(v772, v783) { Ok(v) => v, Err(e) => return Err(e) };
more_157_eo__24eo_5fprog_5fconcat_5fcprop(s, v771, v784, a0, v4, v7, v770, v757, v756, v752, v747, v746, v745, v400)
}
pub(super) fn more_155_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v403: Term, v410: Term, v412: Term, v402: Term, a0: Term, v4: Term, v7: Term, v401: Term, v24: Term, v400: Term) -> CheckResult<Term> {
let v413 = match s.builtin_list(EvalOp::ListNth, &[v403, v410, v412]) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v402, v413) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match if_32_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.literal(Lit::Numeral(v425)) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.builtin_list(EvalOp::ListNth, &[v417, v424, v426]) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.apply(v416, v427) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.apply(v415, v428) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.literal(Lit::Numeral(v430)) { Ok(v) => v, Err(e) => return Err(e) };
let v552 = match if_43_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v583 = match if_46_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v584 = match eo__24str_5foverlap_5frec(s, v552, v583) { Ok(v) => v, Err(e) => return Err(e) };
let v585 = match s.builtin_core(EvalOp::Add, &[v431, v584]) { Ok(v) => v, Err(e) => return Err(e) };
let v586 = match s.apply(v429, v585) { Ok(v) => v, Err(e) => return Err(e) };
let v587 = match s.apply(v414, v586) { Ok(v) => v, Err(e) => return Err(e) };
let v588 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v589 = match s.literal(Lit::Numeral(v588)) { Ok(v) => v, Err(e) => return Err(e) };
let v710 = match if_57_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v741 = match if_60_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v742 = match eo__24str_5foverlap_5frec(s, v710, v741) { Ok(v) => v, Err(e) => return Err(e) };
let v743 = match s.builtin_core(EvalOp::Add, &[v589, v742]) { Ok(v) => v, Err(e) => return Err(e) };
let v744 = match s.apply(v587, v743) { Ok(v) => v, Err(e) => return Err(e) };
let v745 = match s.apply(v401, v744) { Ok(v) => v, Err(e) => return Err(e) };
more_156_eo__24eo_5fprog_5fconcat_5fcprop(s, v24, a0, v4, v7, v745, v400)
}
pub(super) fn more_154_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v66: Term, v79: Term, a0: Term, v4: Term, v7: Term, v65: Term, v52: Term, v51: Term, v47: Term, v42: Term, v41: Term, v24: Term) -> CheckResult<Term> {
let v80 = match s.apply(v66, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(v81)) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match if_13_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match if_16_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match eo__24str_5foverlap_5frec(s, v203, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.builtin_core(EvalOp::Add, &[v82, v235]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v80, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v65, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Numeral(v239)) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match if_27_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match if_30_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match eo__24str_5foverlap_5frec(s, v361, v392) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.builtin_core(EvalOp::Add, &[v240, v393]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.apply(v238, v394) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v52, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v51, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v47, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.apply(v42, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v41, v399) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match if_31_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.literal(Lit::Numeral(v411)) { Ok(v) => v, Err(e) => return Err(e) };
more_155_eo__24eo_5fprog_5fconcat_5fcprop(s, v403, v410, v412, v402, a0, v4, v7, v401, v24, v400)
}
pub(super) fn if_158_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, condition: Term, v24: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v48, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match if_1_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(v62)) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.builtin_list(EvalOp::ListNth, &[v54, v61, v63]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v53, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match if_2_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListNth, &[v68, v75, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v67, v78) { Ok(v) => v, Err(e) => return Err(e) };
more_154_eo__24eo_5fprog_5fconcat_5fcprop(s, v66, v79, a0, v4, v7, v65, v52, v51, v47, v42, v41, v24)
}
Some(false) => {
let v1109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1110 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1111 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1118 = match if_91_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1119 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1120 = match s.literal(Lit::Numeral(v1119)) { Ok(v) => v, Err(e) => return Err(e) };
let v1121 = match s.builtin_list(EvalOp::ListNth, &[v1111, v1118, v1120]) { Ok(v) => v, Err(e) => return Err(e) };
let v1122 = match s.apply(v1110, v1121) { Ok(v) => v, Err(e) => return Err(e) };
let v1123 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v1124 = match s.literal(Lit::Numeral(v1123)) { Ok(v) => v, Err(e) => return Err(e) };
let v1125 = match s.apply(v1122, v1124) { Ok(v) => v, Err(e) => return Err(e) };
let v1126 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v1127 = match s.literal(Lit::Numeral(v1126)) { Ok(v) => v, Err(e) => return Err(e) };
let v1248 = match if_102_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v1279 = match if_105_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1280 = match eo__24str_5foverlap_5frec(s, v1248, v1279) { Ok(v) => v, Err(e) => return Err(e) };
let v1281 = match s.builtin_core(EvalOp::Add, &[v1127, v1280]) { Ok(v) => v, Err(e) => return Err(e) };
let v1282 = match s.apply(v1125, v1281) { Ok(v) => v, Err(e) => return Err(e) };
let v1283 = match s.apply(v1109, v1282) { Ok(v) => v, Err(e) => return Err(e) };
let v1284 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1285 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1286 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1287 = match s.apply(v1286, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1288 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1289 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1290 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1297 = match if_106_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v4) { Ok(v) => v, Err(e) => return Err(e) };
more_151_eo__24eo_5fprog_5fconcat_5fcprop(s, v1290, v1297, v1289, a0, v4, v7, v1288, v1287, v24, v1285, v1284, v1283)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_159_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, v38: Term, v24: Term, a0: Term, v4: Term, v7: Term) -> CheckResult<Term> {
if v38 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v38) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v1825 = match if_158_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v24, a0, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v1826 = match s.apply(v40, v1825) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1826)
}
pub(super) fn case_0_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
let v26 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(v26)) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v27 { return Ok(None); }
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match if_0_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListNth, &[v28, v35, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v1827 = match requires_159_eo__24eo_5fprog_5fconcat_5fcprop(s, v38, v24, a0, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1827))
}
pub(super) fn body_eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_concat_cprop"
pub fn eo__24eo_5fprog_5fconcat_5fcprop(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fconcat_5fcprop(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_96_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2econcat_5fcprop, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fconcat_5fcprop(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v140: Term, v146: Term, v139: Term, v138: Term, v7: Term, v137: Term, v136: Term) -> CheckResult<Term> {
let v147 = match s.apply(v140, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v139, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v138, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v137, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v151, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v136, v153) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v154)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v109: Term, v120: Term, v22: Term, v7: Term, v108: Term, v98: Term, v96: Term) -> CheckResult<Term> {
let v121 = match s.apply(v109, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(v126)) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v125, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match eo__24eo_5ftypeof(s, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24eo_5fnil(s, v122, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v121, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v108, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v98, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v96, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v7) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5fdecompose(s, v140, v146, v139, v138, v7, v137, v136)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v24: Term, v73: Term, v22: Term, v7: Term) -> CheckResult<Term> {
let v74 = match s.apply(v24, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v81, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v80, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v78, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v77, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v76, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v75, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v92, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v74, v94) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v95)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, v46: Term, v48: Term, v7: Term, v45: Term, v43: Term, v42: Term, v22: Term, v41: Term, v26: Term, v24: Term) -> CheckResult<Term> {
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v43, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v42, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Numeral(v59)) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v61, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v56, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match eo__24eo_5ftypeof(s, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match eo__24eo_5fnil(s, v55, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v54, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v41, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v26, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstring_5fdecompose(s, v24, v73, v22, v7)
}
pub(super) fn if_4_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, condition: Term, v22: Term, v7: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(v31)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v33, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v28, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v27, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstring_5fdecompose(s, v46, v48, v7, v45, v43, v42, v22, v41, v26, v24)
}
Some(false) => {
let v96 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(v103)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v102, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v100, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v99, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v113, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v110, v119) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fdecompose(s, v109, v120, v22, v7, v108, v98, v96)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(v9)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v10 { return Ok(None); }
let v11 = match s.destruct(Constructor::eo__24eo_5fpf, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v15 != v7 { return Ok(None); }
let v155 = match if_4_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, v22, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v155))
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_decompose"
pub fn eo__24eo_5fprog_5fstring_5fdecompose(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fdecompose(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_97_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fdecompose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v8 else { return Ok(None); }
;
let v9 = fields[0];
let v10 = fields[1];
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fpf, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fpf, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5fprog_5fstring_5fdecompose(s, v2, v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, v10: Term, v11: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__40witness_5fstring_5flength, &[v15, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v12, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, v6: Term, v7: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v6 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(v8)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Gt, &[a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match requires_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s, v10, v11, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Gt, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_1_eo__24eo_5fprog_5fexists_5fstring_5flength(s, v6, v7, a2, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn body_eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fexists_5fstring_5flength(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_exists_string_length"
pub fn eo__24eo_5fprog_5fexists_5fstring_5flength(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fexists_5fstring_5flength(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_98_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eexists_5fstring_5flength, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = fields[1];
let v7 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v11 { return Ok(None); }
let v12 = match eo__24eo_5fprog_5fexists_5fstring_5flength(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, v24: Term, v19: Term, v8: Term) -> CheckResult<Option<Term>> {
let v25 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v8, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(v5)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v10, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v9, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s, v24, v19, v8)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fcode_5finj(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_code_inj"
pub fn eo__24eo_5fprog_5fstring_5fcode_5finj(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fcode_5finj(s, a0, a1);
s.leave();
result
}
pub(super) fn case_99_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fcode_5finj, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.destruct(Constructor::eo__24emb_5fal_2econs, v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = fields[1];
let v7 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a3 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fprog_5fstring_5fcode_5finj(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_seq_unit_inj"
pub fn eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, a0);
s.leave();
result
}
pub(super) fn case_100_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fseq_5funit_5finj, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fstring_5fseq_5funit_5finj(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v9 else { return Ok(None); }
;
let v10 = fields[0];
let v11 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
if v16 != v7 { return Ok(None); }
let v18 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_inter"
pub fn eo__24eo_5fprog_5fre_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5finter(s, a0, a1);
s.leave();
result
}
pub(super) fn case_101_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fpf, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fprog_5fre_5finter(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v29])))
}
pub(super) fn case_1_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn step_eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5fre_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5fconcat(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5fre_5fconcat(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5fre_5fconcat(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$mk_re_concat"
pub fn eo__24mk_5fre_5fconcat(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(929), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fre_5fconcat(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(929), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListRev, &[v2, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24mk_5fre_5fconcat(s, v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5fconcat(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_concat"
pub fn eo__24eo_5fprog_5fre_5fconcat(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5fconcat(s, a0);
s.leave();
result
}
pub(super) fn case_102_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5fconcat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fmk_5fpremise_5flist(s, v2, a3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fpf, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fprog_5fre_5fconcat(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, v57: Term, v58: Term, v39: Term, v34: Term) -> CheckResult<Option<Term>> {
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v39, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v34, v60) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v61))
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, v12: Term, v19: Term, v26: Term, v2: Term, v34: Term) -> CheckResult<Option<Term>> {
let v35 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v47, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v45, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v43, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v41, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v40, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fpos_5fstar(s, v57, v58, v39, v34)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
let v21 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v28 { return Ok(None); }
let v29 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, v12, v19, v26, v2, v34)
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_pos_star"
pub fn eo__24mk_5fre_5funfold_5fpos_5fstar(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, v23: Term, v28: Term, v17: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v23, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v17, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
// EO program "$re_unfold_pos_concat_rec"
pub fn eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(957), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(957), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[a3, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24pair_5ffirst(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v13, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Add, &[a3, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24pair_5fsecond(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v20, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_2_eo__24re_5funfold_5fpos_5fconcat_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, &[a0, a2, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_core(EvalOp::Add, &[a3, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24pair_5ffirst(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v7, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__40re_5funfold_5fpos_5fcomponent, &[a0, a2, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(v24)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::Add, &[a3, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v2, a2, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24pair_5fsecond(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5funfold_5fpos_5fconcat_5frec(s, v23, v28, v17)
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v42: Term, v48: Term, v41: Term, v37: Term, a0: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v42, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v41, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v37, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Numeral(v56)) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v29, v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24mk_5fre_5funfold_5fpos_5fstar(s, a0, v2, v58) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v59))
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, v24: Term, v23: Term, v15: Term, v11: Term, v2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v25 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v15, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v11, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v32, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v30, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v44, v47) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fpos(s, v42, v48, v41, v37, a0, v29, v2)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fre_5funfold_5fpos(s, v24, v23, v15, v11, v2, a0)
}
pub(super) fn if_2_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, condition: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(v27)) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v23, v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24pair_5ffirst(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v20, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
Some(false) => {
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(v41)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v37, v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24pair_5ffirst(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v34, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v32, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Numeral(v53)) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v49, v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24pair_5fsecond(s, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v46, v56) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(v13)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24re_5funfold_5fpos_5fconcat_5frec(s, a0, v9, v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24pair_5fsecond(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match if_2_eo__24mk_5fre_5funfold_5fpos(s, v18, a0, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5funfold_5fpos(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_pos"
pub fn eo__24mk_5fre_5funfold_5fpos(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fpos(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.unapply(v3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v6, v7)) = v5 else { return Ok(None); }
;
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match eo__24mk_5fre_5funfold_5fpos(s, v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fpos(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_pos"
pub fn eo__24eo_5fprog_5fre_5funfold_5fpos(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fpos(s, a0);
s.leave();
result
}
pub(super) fn case_103_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fpos, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fre_5funfold_5fpos(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn cases_12_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_96_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_97_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_98_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_99_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_100_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_101_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_102_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_103_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListRev, &[v13, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(v1)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_3_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::Length, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
// EO program "$str_fixed_len_re"
pub fn eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1043), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5ffixed_5flen_5fre(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1043), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_4_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_5_eo__24str_5ffixed_5flen_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_4_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_1_eo__24str_5ffixed_5flen_5fre(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_5_eo__24str_5ffixed_5flen_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_3_eo__24str_5ffixed_5flen_5fre(s, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn requires_0_eo__24str_5ffixed_5flen_5fre(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn if_1_eo__24str_5ffixed_5flen_5fre(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_0_eo__24str_5ffixed_5flen_5fre(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24str_5ffixed_5flen_5fre(s: &mut Store, v10: Term, v11: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
pub(super) fn if_3_eo__24str_5ffixed_5flen_5fre(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match requires_2_eo__24str_5ffixed_5flen_5fre(s, v10, v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v5: Term, v76: Term, v72: Term, v68: Term, v2: Term, v67: Term, v66: Term, v65: Term) -> CheckResult<Term> {
let v77 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v72, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v68, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_list(EvalOp::ListSingletonElim, &[v81, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v67, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v66, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v85, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v65, v87) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v88)
}
pub(super) fn if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListRev, &[v42, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
Some(false) => {
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, v29: Term, v31: Term, a0: Term, v5: Term, v27: Term, a2: Term, v2: Term, v26: Term, v25: Term, v24: Term) -> CheckResult<Term> {
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v32, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v27, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_list(EvalOp::ListSingletonElim, &[v41, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v40, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v26, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v25, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v24, v50) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
pub(super) fn if_3_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v9, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v8, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v7, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(v30)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v29, v31, a0, v5, v27, a2, v2, v26, v25, v24)
}
Some(false) => {
let v52 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(v57)) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v59, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v54, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v53, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v52, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24str_5ffixed_5flen_5fre(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v70, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v73, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v5, v76, v72, v68, v2, v67, v66, v65)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v89 = match if_3_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a2, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v89))
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_neg_concat_fixed"
pub fn eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v15 = match if_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24mk_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v11, v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_neg_concat_fixed"
pub fn eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, a0, a1);
s.leave();
result
}
pub(super) fn case_104_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fneg_5fconcat_5ffixed, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v1 else { return Ok(None); }
;
let v2 = fields[0];
let v3 = fields[1];
let v4 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v4 { return Ok(None); }
let v5 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v5 else { return Ok(None); }
;
let v6 = fields[0];
let v7 = fields[1];
let v8 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v8 { return Ok(None); }
let v9 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fpf, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24eo_5fprog_5fre_5funfold_5fneg_5fconcat_5ffixed(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_2_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v66: Term, v74: Term, v60: Term, v2: Term, v59: Term, v58: Term, v57: Term, v41: Term, v31: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v75 = match s.apply(v66, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v60, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v76, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v59, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v58, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v81, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v57, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v41, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v31, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v21, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v12, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v88, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v11, v90) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v91))
}
pub(super) fn more_1_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v50: Term, v49: Term, v44: Term, v2: Term, v43: Term, v42: Term, a0: Term, v41: Term, v31: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__24emb_5fVar, &[v50, v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v44, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v43, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v42, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__24emb_5fVar, &[v71, v72]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v70, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fre_5funfold_5fneg(s, v66, v74, v60, v2, v59, v58, v57, v41, v31, v21, v12, v11)
}
pub(super) fn more_0_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v24: Term, v23: Term, v22: Term, a0: Term, v2: Term, v21: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fVar, &[v24, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(v28)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v22, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24emb_5fVar, &[v37, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v32, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(v47)) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fre_5funfold_5fneg(s, v50, v49, v44, v2, v43, v42, a0, v41, v31, v21, v12, v11)
}
pub(super) fn case_0_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24emb_5fVar, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v13, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fre_5funfold_5fneg(s, v24, v23, v22, a0, v2, v21, v12, v11)
}
pub(super) fn more_5_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, v75: Term, v76: Term, v51: Term, v35: Term, v25: Term, v15: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v75, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v51, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v35, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v25, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v15, v80) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v81))
}
pub(super) fn more_4_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, v2: Term, v52: Term, v51: Term, v35: Term, v25: Term, v15: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__24emb_5fVar, &[v57, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v56, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__24emb_5fVar, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v64, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v60, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v54, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.builtin_list(EvalOp::ListSingletonElim, &[v71, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v70, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v53, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v52, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24mk_5fre_5funfold_5fneg(s, v75, v76, v51, v35, v25, v15)
}
pub(super) fn more_3_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, v27: Term, v26: Term, v5: Term, v2: Term, v25: Term, v15: Term) -> CheckResult<Option<Term>> {
let v28 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24emb_5fVar, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v26, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(v41)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__24emb_5fVar, &[v44, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v43, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v38, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v37, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v36, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5fre_5funfold_5fneg(s, a0, v2, v52, v51, v35, v25, v15)
}
pub(super) fn case_1_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5fVar, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v7, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24emb_5fVar, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fre_5funfold_5fneg(s, a0, v27, v26, v5, v2, v25, v15)
}
pub(super) fn body_eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fre_5funfold_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fre_5funfold_5fneg(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_re_unfold_neg"
pub fn eo__24mk_5fre_5funfold_5fneg(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fre_5funfold_5fneg(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match eo__24mk_5fre_5funfold_5fneg(s, v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn body_eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_5funfold_5fneg(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re_unfold_neg"
pub fn eo__24eo_5fprog_5fre_5funfold_5fneg(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_5funfold_5fneg(s, a0);
s.leave();
result
}
pub(super) fn case_105_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funfold_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fre_5funfold_5fneg(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v41: Term, v53: Term, v31: Term, v24: Term, v23: Term) -> CheckResult<Option<Term>> {
let v54 = match s.apply(v41, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v31, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v24, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v23, v58) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v59))
}
pub(super) fn case_0_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v6, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(v17)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v13, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v5, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_1_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn body_eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_mk_ext_deq"
pub fn eo__24str_5fmk_5fext_5fdeq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fmk_5fext_5fdeq(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_0_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, v11: Term, v8: Term, v28: Term, v25: Term, v24: Term, v23: Term) -> CheckResult<Option<Term>> {
let v29 = match eo__24eo_5ftypeof(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24str_5fmk_5fext_5fdeq(s, v11, v8, v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v25, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v32, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v43, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v42, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v51, v52) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstring_5fext(s, v41, v53, v31, v24, v23)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40strings_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5fext(s, v11, v8, v28, v25, v24, v23)
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5fext(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_ext"
pub fn eo__24eo_5fprog_5fstring_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5fext(s, a0);
s.leave();
result
}
pub(super) fn case_106_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5fext, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fstring_5fext(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_1_eo__24str_5freduction_5fpred(s: &mut Store, v36: Term, v51: Term, v5: Term, v2: Term, v35: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v52 = match s.apply(v36, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__24emb_5fVar, &[v58, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v57, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v55, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v54, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v53, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v52, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v35, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v23, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v14, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v13, v74) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v75))
}
pub(super) fn more_0_eo__24str_5freduction_5fpred(s: &mut Store, v26: Term, v25: Term, v24: Term, v5: Term, v2: Term, v23: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v27 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24emb_5fVar, &[v27, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(v31)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v25, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v24, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24emb_5fVar, &[v39, v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v42, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v37, v50) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5freduction_5fpred(s, v36, v51, v5, v2, v35, v23, v14, v13)
}
pub(super) fn case_0_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24emb_5fVar, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v15, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5freduction_5fpred(s, v26, v25, v24, v5, v2, v23, v14, v13)
}
pub(super) fn more_10_eo__24str_5freduction_5fpred(s: &mut Store, v233: Term, v232: Term, v224: Term) -> CheckResult<Option<Term>> {
let v234 = match eo__24seq_5fempty(s, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v232, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v224, v235) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v236))
}
pub(super) fn more_9_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v209: Term, v208: Term, v207: Term, v206: Term, v205: Term, v117: Term, v102: Term, v36: Term) -> CheckResult<Option<Term>> {
let v210 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v210, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v211, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v212, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v209, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v208, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v207, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v216, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v206, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v218, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v205, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v117, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v102, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v36, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v228, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v226, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v225, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24str_5freduction_5fpred(s, v233, v232, v224)
}
pub(super) fn more_8_eo__24str_5freduction_5fpred(s: &mut Store, v181: Term, v183: Term, v5: Term, v2: Term, v180: Term, v169: Term, v168: Term, v167: Term, v166: Term, v165: Term, v118: Term, v8: Term, v117: Term, v102: Term, v36: Term) -> CheckResult<Option<Term>> {
let v184 = match s.apply(v181, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v187, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Numeral(v189)) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v186, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v184, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v180, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v169, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v168, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v167, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.literal(Lit::Numeral(v198)) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v197, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v166, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v201, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v165, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v118, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24str_5freduction_5fpred(s, v8, v5, v2, v209, v208, v207, v206, v205, v117, v102, v36)
}
pub(super) fn more_7_eo__24str_5freduction_5fpred(s: &mut Store, v157: Term, v2: Term, v156: Term, v154: Term, v150: Term, v119: Term, v8: Term, v5: Term, v118: Term, v117: Term, v102: Term, v36: Term) -> CheckResult<Option<Term>> {
let v158 = match s.apply(v157, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.literal(Lit::Numeral(v159)) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v158, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v156, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v154, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v150, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v119, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v172, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v174, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v175, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v173, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v171, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v182, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24str_5freduction_5fpred(s, v181, v183, v5, v2, v180, v169, v168, v167, v166, v165, v118, v8, v117, v102, v36)
}
pub(super) fn more_6_eo__24str_5freduction_5fpred(s: &mut Store, v124: Term, v132: Term, v8: Term, v5: Term, v2: Term, v122: Term, v121: Term, v120: Term, v119: Term, v118: Term, v117: Term, v102: Term, v36: Term) -> CheckResult<Option<Term>> {
let v133 = match s.apply(v124, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v135, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v134, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v138, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.literal(Lit::Numeral(v142)) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v141, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v139, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v137, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v133, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v122, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v121, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v120, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v151, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24str_5freduction_5fpred(s, v157, v2, v156, v154, v150, v119, v8, v5, v118, v117, v102, v36)
}
pub(super) fn more_5_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v106: Term, v105: Term, v104: Term, v103: Term, v2: Term, v102: Term, v36: Term) -> CheckResult<Option<Term>> {
let v107 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(v109)) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v108, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v106, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v105, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v104, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v103, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(v129)) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v128, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v126, v131) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24str_5freduction_5fpred(s, v124, v132, v8, v5, v2, v122, v121, v120, v119, v118, v117, v102, v36)
}
pub(super) fn more_4_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v81: Term, v74: Term, v70: Term, v59: Term, v58: Term, v8: Term, v5: Term, v57: Term, v49: Term, v39: Term, v37: Term, v2: Term, v36: Term) -> CheckResult<Option<Term>> {
let v82 = match s.apply(v76, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v74, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v70, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v59, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v58, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Numeral(v91)) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v90, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v88, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match eo__24eo_5ftypeof(s, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24eo_5fnil(s, v87, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v86, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v57, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v49, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v39, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v37, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24str_5freduction_5fpred(s, v8, v5, v106, v105, v104, v103, v2, v102, v36)
}
pub(super) fn more_3_eo__24str_5freduction_5fpred(s: &mut Store, v51: Term, v55: Term, v50: Term, v8: Term, v5: Term, v2: Term, v49: Term, v39: Term, v37: Term, v36: Term) -> CheckResult<Option<Term>> {
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v50, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(v66)) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v65, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v63, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v61, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v71, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(v79)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24str_5freduction_5fpred(s, v76, v81, v74, v70, v59, v58, v8, v5, v57, v49, v39, v37, v2, v36)
}
pub(super) fn more_2_eo__24str_5freduction_5fpred(s: &mut Store, v25: Term, v30: Term, v24: Term, v17: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v31 = match s.apply(v25, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v17, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v10, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(v44)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v41, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v40, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24str_5freduction_5fpred(s, v51, v55, v50, v8, v5, v2, v49, v39, v37, v36)
}
pub(super) fn case_1_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(v28)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24str_5freduction_5fpred(s, v25, v30, v24, v17, v10, v8, v5, v2)
}
pub(super) fn more_26_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v407: Term, v2: Term, v406: Term, v403: Term, v5: Term, v402: Term, v388: Term, v387: Term, v386: Term, v385: Term, v383: Term, v375: Term, v374: Term, v281: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v408 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.apply(v408, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.apply(v407, v409) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.apply(v410, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.apply(v406, v411) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.apply(v403, v412) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v413, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.literal(Lit::Numeral(v415)) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.apply(v414, v416) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.apply(v402, v417) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v388, v418) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.apply(v387, v419) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.apply(v386, v420) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.literal(Lit::Numeral(v422)) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.apply(v421, v423) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.apply(v385, v424) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v383, v425) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.apply(v375, v426) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.apply(v427, v428) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.apply(v374, v429) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.apply(v281, v430) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.apply(v74, v431) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.apply(v57, v432) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v433))
}
pub(super) fn more_25_eo__24str_5freduction_5fpred(s: &mut Store, v376: Term, v382: Term, v2: Term, v8: Term, v5: Term, v375: Term, v374: Term, v281: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v383 = match s.apply(v376, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.apply(v384, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.apply(v390, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.apply(v391, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.apply(v394, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v393, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v396, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v392, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.apply(v389, v398) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.literal(Lit::Numeral(v400)) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v399, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.apply(v404, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.apply(v405, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24str_5freduction_5fpred(s, v8, v407, v2, v406, v403, v5, v402, v388, v387, v386, v385, v383, v375, v374, v281, v74, v57)
}
pub(super) fn more_24_eo__24str_5freduction_5fpred(s: &mut Store, v357: Term, v2: Term, v353: Term, v350: Term, v5: Term, v349: Term, v335: Term, v334: Term, v333: Term, v318: Term, v284: Term, v283: Term, v282: Term, v8: Term, v281: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v358 = match s.apply(v357, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v353, v358) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v350, v359) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v360, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.literal(Lit::Numeral(v362)) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.apply(v361, v363) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.apply(v349, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.apply(v335, v365) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match eo__24eo_5ftypeof(s, v366) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match eo__24eo_5fnil(s, v334, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.apply(v333, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.apply(v318, v369) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v284, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.apply(v371, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v283, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v282, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.apply(v378, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.apply(v379, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.apply(v380, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.apply(v377, v381) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24str_5freduction_5fpred(s, v376, v382, v2, v8, v5, v375, v374, v281, v74, v57)
}
pub(super) fn more_23_eo__24str_5freduction_5fpred(s: &mut Store, v319: Term, v332: Term, v8: Term, v2: Term, v5: Term, v318: Term, v284: Term, v283: Term, v282: Term, v281: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v333 = match s.apply(v319, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v337, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.apply(v338, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v341, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v340, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v343, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v339, v344) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v336, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.literal(Lit::Numeral(v347)) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.apply(v346, v348) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v351, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.apply(v352, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.apply(v355, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v354, v356) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24str_5freduction_5fpred(s, v357, v2, v353, v350, v5, v349, v335, v334, v333, v318, v284, v283, v282, v8, v281, v74, v57)
}
pub(super) fn more_22_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v305: Term, v2: Term, v304: Term, v301: Term, v5: Term, v300: Term, v286: Term, v285: Term, v284: Term, v283: Term, v282: Term, v281: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v306 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v306, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v305, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v308, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v304, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v301, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v311, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.literal(Lit::Numeral(v313)) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v312, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v300, v315) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v286, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v285, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v320, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.literal(Lit::Numeral(v322)) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v321, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v326, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v325, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.literal(Lit::Numeral(v329)) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v328, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v324, v331) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24str_5freduction_5fpred(s, v319, v332, v8, v2, v5, v318, v284, v283, v282, v281, v74, v57)
}
pub(super) fn more_21_eo__24str_5freduction_5fpred(s: &mut Store, v75: Term, v280: Term, v8: Term, v2: Term, v5: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v281 = match s.apply(v75, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.apply(v288, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v289, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v292, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v291, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v294, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v290, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v287, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.literal(Lit::Numeral(v298)) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v297, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v302, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v303, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24str_5freduction_5fpred(s, v8, v305, v2, v304, v301, v5, v300, v286, v285, v284, v283, v282, v281, v74, v57)
}
pub(super) fn more_20_eo__24str_5freduction_5fpred(s: &mut Store, v254: Term, v8: Term, v2: Term, v5: Term, v243: Term, v242: Term, v241: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v255 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Numeral(v255)) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v254, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v259, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v260, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v263, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v262, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v265, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v261, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v258, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v268, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::Numeral(v270)) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v269, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v257, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v243, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match eo__24eo_5ftypeof(s, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match eo__24eo_5fnil(s, v242, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v241, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v122, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v120, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v86, v279) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24str_5freduction_5fpred(s, v75, v280, v8, v2, v5, v74, v57)
}
pub(super) fn more_19_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v229: Term, v193: Term, v180: Term, v124: Term, v123: Term, v8: Term, v2: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v230 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v231, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v230, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.literal(Lit::Numeral(v234)) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v233, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v229, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v193, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v180, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v124, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v123, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v245, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v246, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v249, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v248, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v251, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v247, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v244, v253) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24str_5freduction_5fpred(s, v254, v8, v2, v5, v243, v242, v241, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_18_eo__24str_5freduction_5fpred(s: &mut Store, v201: Term, v203: Term, v2: Term, v200: Term, v197: Term, v8: Term, v5: Term, v196: Term, v195: Term, v194: Term, v193: Term, v180: Term, v124: Term, v123: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v204 = match s.apply(v201, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v200, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v197, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.literal(Lit::Numeral(v208)) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v207, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v212, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v213, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v216, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v215, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v218, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v214, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v211, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v221, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::Numeral(v223)) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v222, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v210, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v196, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v195, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v194, v228) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24str_5freduction_5fpred(s, v5, v229, v193, v180, v124, v123, v8, v2, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_17_eo__24str_5freduction_5fpred(s: &mut Store, v135: Term, v179: Term, v8: Term, v2: Term, v5: Term, v124: Term, v123: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v180 = match s.apply(v135, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v184, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v187, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v186, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v185, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v182, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v181, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v198, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v199, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v202, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24str_5freduction_5fpred(s, v201, v203, v2, v200, v197, v8, v5, v196, v195, v194, v193, v180, v124, v123, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_16_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v153: Term, v5: Term, v152: Term, v138: Term, v137: Term, v136: Term, v135: Term, v124: Term, v123: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v154 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v154, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v158, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v157, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v156, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v153, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v163, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Numeral(v165)) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v164, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v152, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v138, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v137, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v136, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v173, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v172, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(v176)) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v175, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v171, v178) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24str_5freduction_5fpred(s, v135, v179, v8, v2, v5, v124, v123, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_15_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v128: Term, v125: Term, v5: Term, v124: Term, v123: Term, v122: Term, v120: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v129 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v129, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v132, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v128, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v125, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v140, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v143, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v142, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v139, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Numeral(v150)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v149, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24str_5freduction_5fpred(s, v8, v2, v153, v5, v152, v138, v137, v136, v135, v124, v123, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_14_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v2: Term, v103: Term, v5: Term, v102: Term, v88: Term, v87: Term, v86: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v104 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v106, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v103, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(v115)) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v102, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v88, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v87, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v121, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v127, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24str_5freduction_5fpred(s, v8, v2, v128, v125, v5, v124, v123, v122, v120, v86, v75, v74, v57)
}
pub(super) fn more_13_eo__24str_5freduction_5fpred(s: &mut Store, v78: Term, v2: Term, v8: Term, v76: Term, v5: Term, v75: Term, v74: Term, v57: Term) -> CheckResult<Option<Term>> {
let v79 = match s.apply(v78, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v79, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v76, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v92, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v89, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(v100)) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v99, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24str_5freduction_5fpred(s, v8, v2, v103, v5, v102, v88, v87, v86, v75, v74, v57)
}
pub(super) fn more_12_eo__24str_5freduction_5fpred(s: &mut Store, v53: Term, v45: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v54 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v45, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24seq_5fempty(s, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v60, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v58, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v66, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v65, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v64, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24str_5freduction_5fpred(s, v78, v2, v8, v76, v5, v75, v74, v57)
}
pub(super) fn more_11_eo__24str_5freduction_5fpred(s: &mut Store, v28: Term, v2: Term, v8: Term, v27: Term, v26: Term, v10: Term, v5: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v27, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(v36)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v34, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v33, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v26, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v10, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v47, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24str_5freduction_5fpred(s, v53, v45, v5, v8, v2)
}
pub(super) fn case_2_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v16, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v12, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v11, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24str_5freduction_5fpred(s, v28, v2, v8, v27, v26, v10, v5)
}
pub(super) fn more_38_eo__24str_5freduction_5fpred(s: &mut Store, v263: Term, v318: Term, v262: Term, v148: Term, v40: Term, v8: Term, v5: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v319 = match s.apply(v263, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v319, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v262, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v148, v322) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v40, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v327, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.apply(v328, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v329, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v326, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v325, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v332, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v324, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v35, v334) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v335))
}
pub(super) fn more_37_eo__24str_5freduction_5fpred(s: &mut Store, v291: Term, v287: Term, v282: Term, v8: Term, v5: Term, v281: Term, v265: Term, v264: Term, v263: Term, v262: Term, v148: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v292 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.literal(Lit::Numeral(v292)) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v291, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v287, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v282, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v299, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.literal(Lit::Numeral(v301)) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v300, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.apply(v304, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v305, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.literal(Lit::Numeral(v307)) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v306, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v303, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v298, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match eo__24eo_5ftypeof(s, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match eo__24eo_5fnil(s, v297, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v296, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v281, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v265, v315) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v316, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v264, v317) { Ok(v) => v, Err(e) => return Err(e) };
more_38_eo__24str_5freduction_5fpred(s, v263, v318, v262, v148, v40, v8, v5, v2, v35)
}
pub(super) fn more_36_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v264: Term, v263: Term, v262: Term, v148: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v265 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v268, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::Numeral(v270)) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v269, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v273, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v274, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Numeral(v276)) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v275, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v272, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v267, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v266, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v283, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.literal(Lit::Numeral(v285)) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v284, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v289, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v288, v290) { Ok(v) => v, Err(e) => return Err(e) };
more_37_eo__24str_5freduction_5fpred(s, v291, v287, v282, v8, v5, v281, v265, v264, v263, v262, v148, v40, v2, v35)
}
pub(super) fn more_35_eo__24str_5freduction_5fpred(s: &mut Store, v177: Term, v238: Term, v176: Term, v8: Term, v5: Term, v175: Term, v173: Term, v157: Term, v149: Term, v148: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v239 = match s.apply(v177, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v176, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v243, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.literal(Lit::Numeral(v245)) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v244, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v249, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.literal(Lit::Numeral(v251)) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v250, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v247, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v242, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match eo__24eo_5ftypeof(s, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match eo__24eo_5fnil(s, v241, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v240, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v175, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v173, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v157, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v149, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_36_eo__24str_5freduction_5fpred(s, v8, v5, v264, v263, v262, v148, v40, v2, v35)
}
pub(super) fn more_34_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v211: Term, v210: Term, v206: Term, v177: Term, v176: Term, v175: Term, v173: Term, v157: Term, v149: Term, v148: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v212 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v214, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Numeral(v216)) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v215, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v219, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v220, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.literal(Lit::Numeral(v222)) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v221, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v218, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v213, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v212, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v211, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v229, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.literal(Lit::Numeral(v233)) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v232, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v228, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v210, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v206, v237) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24str_5freduction_5fpred(s, v177, v238, v176, v8, v5, v175, v173, v157, v149, v148, v40, v2, v35)
}
pub(super) fn more_33_eo__24str_5freduction_5fpred(s: &mut Store, v184: Term, v8: Term, v5: Term, v182: Term, v181: Term, v180: Term, v179: Term, v177: Term, v176: Term, v175: Term, v173: Term, v157: Term, v149: Term, v148: Term, v40: Term, v2: Term, v35: Term) -> CheckResult<Option<Term>> {
let v185 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Numeral(v185)) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v184, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.literal(Lit::Numeral(v191)) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v190, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v187, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v182, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v181, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v180, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v199, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v198, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.literal(Lit::Numeral(v202)) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v201, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v197, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v179, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v208, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v207, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24str_5freduction_5fpred(s, v8, v5, v211, v210, v206, v177, v176, v175, v173, v157, v149, v148, v40, v2, v35)
}
pub(super) fn more_32_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v158: Term, v2: Term, v157: Term, v149: Term, v148: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v159 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::Numeral(v162)) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v161, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v165, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v166, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.literal(Lit::Numeral(v168)) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v167, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v164, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v159, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v158, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v174, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24str_5freduction_5fpred(s, v184, v8, v5, v182, v181, v180, v179, v177, v176, v175, v173, v157, v149, v148, v40, v2, v35)
}
pub(super) fn more_31_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v133: Term, v128: Term, v127: Term, v126: Term, v61: Term, v59: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v134 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v134, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v135, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Numeral(v137)) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v136, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v133, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v128, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match eo__24eo_5ftypeof(s, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match eo__24eo_5fnil(s, v127, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v126, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v61, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v59, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v43, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v41, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v153, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v154, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v151, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v150, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24str_5freduction_5fpred(s, v8, v5, v158, v2, v157, v149, v148, v40, v35)
}
pub(super) fn more_30_eo__24str_5freduction_5fpred(s: &mut Store, v106: Term, v5: Term, v104: Term, v99: Term, v98: Term, v97: Term, v96: Term, v92: Term, v63: Term, v62: Term, v8: Term, v61: Term, v59: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v107 = match s.apply(v106, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Numeral(v108)) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v104, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v99, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v98, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v97, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v115, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(v119)) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v118, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v114, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v96, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v92, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v63, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v62, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v129, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24str_5freduction_5fpred(s, v8, v5, v133, v128, v127, v126, v61, v59, v43, v41, v2, v40, v35)
}
pub(super) fn more_29_eo__24str_5freduction_5fpred(s: &mut Store, v68: Term, v80: Term, v67: Term, v66: Term, v5: Term, v65: Term, v8: Term, v63: Term, v62: Term, v61: Term, v59: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v81 = match s.apply(v68, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v67, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v66, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v85, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v84, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Numeral(v88)) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v83, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v65, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24str_5freduction_5fpred(s, v106, v5, v104, v99, v98, v97, v96, v92, v63, v62, v8, v61, v59, v43, v41, v2, v40, v35)
}
pub(super) fn more_28_eo__24str_5freduction_5fpred(s: &mut Store, v53: Term, v50: Term, v45: Term, v44: Term, v5: Term, v8: Term, v43: Term, v41: Term, v2: Term, v40: Term, v35: Term) -> CheckResult<Option<Term>> {
let v54 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(v54)) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v50, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v45, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v44, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(v71)) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v70, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Numeral(v77)) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v76, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v73, v79) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24str_5freduction_5fpred(s, v68, v80, v67, v66, v5, v65, v8, v63, v62, v61, v59, v43, v41, v2, v40, v35)
}
pub(super) fn more_27_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v28: Term, v26: Term, v24: Term, v16: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fnil(s, v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v26, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v24, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v16, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(v48)) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24str_5freduction_5fpred(s, v53, v50, v45, v44, v5, v8, v43, v41, v2, v40, v35)
}
pub(super) fn case_3_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24seq_5fempty(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24str_5freduction_5fpred(s, v2, v28, v26, v24, v16, v8, v5)
}
pub(super) fn more_49_eo__24str_5freduction_5fpred(s: &mut Store, v283: Term, v287: Term, v282: Term) -> CheckResult<Option<Term>> {
let v288 = match s.apply(v283, v287) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v288, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v282, v290) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v291))
}
pub(super) fn more_48_eo__24str_5freduction_5fpred(s: &mut Store, v247: Term, v263: Term, v245: Term, v244: Term, v153: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term, v2: Term) -> CheckResult<Option<Term>> {
let v264 = match s.apply(v247, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v245, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v265, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v244, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v153, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v88, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v270, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v87, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v71, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v59, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v50, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v276, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v49, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v37, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v23, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v10, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v284, v286) { Ok(v) => v, Err(e) => return Err(e) };
more_49_eo__24str_5freduction_5fpred(s, v283, v287, v282)
}
pub(super) fn more_47_eo__24str_5freduction_5fpred(s: &mut Store, v236: Term, v214: Term, v213: Term, v154: Term, v2: Term, v153: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v237 = match parse_int("10") { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.literal(Lit::Numeral(v237)) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v236, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v214, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v240, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v213, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v154, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v246, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.construct(Constructor::eo__24emb_5fVar, &[v251, v252]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v250, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.literal(Lit::Numeral(v256)) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v255, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Numeral(v259)) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v258, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v254, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v249, v262) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24str_5freduction_5fpred(s, v247, v263, v245, v244, v153, v88, v87, v71, v59, v50, v49, v37, v23, v10, v2)
}
pub(super) fn more_46_eo__24str_5freduction_5fpred(s: &mut Store, v208: Term, v210: Term, v177: Term, v155: Term, v2: Term, v154: Term, v153: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v211 = match s.apply(v208, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v177, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v155, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v220, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v219, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v218, v222) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo__24emb_5fVar, &[v224, v225]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v223, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.literal(Lit::Numeral(v228)) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v227, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v217, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v216, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.literal(Lit::Numeral(v233)) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v232, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v215, v235) { Ok(v) => v, Err(e) => return Err(e) };
more_47_eo__24str_5freduction_5fpred(s, v236, v214, v213, v154, v2, v153, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_45_eo__24str_5freduction_5fpred(s: &mut Store, v181: Term, v182: Term, v180: Term, v179: Term, v2: Term, v178: Term, v177: Term, v155: Term, v154: Term, v153: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v183 = match s.construct(Constructor::eo__24emb_5fVar, &[v181, v182]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v180, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.literal(Lit::Numeral(v185)) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v184, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v179, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v193, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v192, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v191, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v190, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.literal(Lit::Numeral(v198)) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v197, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v189, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v201, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v188, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v178, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.literal(Lit::Numeral(v206)) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v205, v207) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.literal(Lit::Numeral(v209)) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24str_5freduction_5fpred(s, v208, v210, v177, v155, v2, v154, v153, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_44_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v156: Term, v155: Term, v154: Term, v153: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v157 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v161, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v160, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v159, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__24emb_5fVar, &[v165, v166]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v164, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.literal(Lit::Numeral(v169)) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v168, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v158, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v157, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::Numeral(v174)) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v173, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v156, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_45_eo__24str_5freduction_5fpred(s, v181, v182, v180, v179, v2, v178, v177, v155, v154, v153, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_43_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v129: Term, v107: Term, v89: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v130 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match parse_int("10") { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Numeral(v132)) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v131, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v136, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__24emb_5fVar, &[v138, v139]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v137, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v135, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v134, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v130, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.literal(Lit::Numeral(v148)) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v147, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v129, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v107, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v89, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24str_5freduction_5fpred(s, v2, v156, v155, v154, v153, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_42_eo__24str_5freduction_5fpred(s: &mut Store, v101: Term, v103: Term, v97: Term, v92: Term, v90: Term, v2: Term, v89: Term, v88: Term, v87: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v97, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v92, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v90, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v112, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v111, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__24emb_5fVar, &[v117, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v116, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(v121)) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v120, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v110, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v109, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(v126)) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v125, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v108, v128) { Ok(v) => v, Err(e) => return Err(e) };
more_43_eo__24str_5freduction_5fpred(s, v2, v129, v107, v89, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_41_eo__24str_5freduction_5fpred(s: &mut Store, v74: Term, v77: Term, v2: Term, v73: Term, v72: Term, v71: Term, v59: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v78 = match s.apply(v74, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v79, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v78, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v73, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v72, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo__24emb_5fVar, &[v94, v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v93, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24str_5freduction_5fpred(s, v101, v103, v97, v92, v90, v2, v89, v88, v87, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_40_eo__24str_5freduction_5fpred(s: &mut Store, v52: Term, v51: Term, v2: Term, v50: Term, v49: Term, v37: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v53 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__24emb_5fVar, &[v53, v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v52, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v56, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v51, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(v67)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v61, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v60, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo__24emb_5fVar, &[v75, v76]) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24str_5freduction_5fpred(s, v74, v77, v2, v73, v72, v71, v59, v50, v49, v37, v23, v10)
}
pub(super) fn more_39_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v26: Term, v24: Term, v23: Term, v10: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v28, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v26, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v24, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Numeral(v40)) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__40strings_5fitos_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v38, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24str_5freduction_5fpred(s, v52, v51, v2, v50, v49, v37, v23, v10)
}
pub(super) fn case_4_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v11, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24str_5freduction_5fpred(s, v2, v26, v24, v23, v10)
}
pub(super) fn more_61_eo__24str_5freduction_5fpred(s: &mut Store, v309: Term, v316: Term, v304: Term, v302: Term, v296: Term, v295: Term, v244: Term, v183: Term, v182: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v317 = match s.apply(v309, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v304, v317) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v302, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.apply(v296, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v320, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v295, v322) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v244, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v183, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v325, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v182, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.apply(v170, v328) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v158, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v149, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v331, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v148, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v139, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v127, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v113, v336) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v337))
}
pub(super) fn more_60_eo__24str_5freduction_5fpred(s: &mut Store, v269: Term, v290: Term, v268: Term, v245: Term, v2: Term, v244: Term, v183: Term, v182: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v291 = match s.apply(v269, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v291, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v268, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v245, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v299, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v298, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v297, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v303, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo__24emb_5fVar, &[v306, v307]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v305, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.literal(Lit::Numeral(v311)) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.apply(v310, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.literal(Lit::Numeral(v314)) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v313, v315) { Ok(v) => v, Err(e) => return Err(e) };
more_61_eo__24str_5freduction_5fpred(s, v309, v316, v304, v302, v296, v295, v244, v183, v182, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_59_eo__24str_5freduction_5fpred(s: &mut Store, v260: Term, v262: Term, v247: Term, v246: Term, v2: Term, v245: Term, v244: Term, v183: Term, v182: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v263 = match s.apply(v260, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v247, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Numeral(v265)) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v264, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v246, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v273, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.construct(Constructor::eo__24emb_5fVar, &[v275, v276]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v274, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.literal(Lit::Numeral(v279)) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v278, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v272, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v271, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.literal(Lit::Numeral(v284)) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v283, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v270, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match parse_int("10") { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.literal(Lit::Numeral(v288)) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v287, v289) { Ok(v) => v, Err(e) => return Err(e) };
more_60_eo__24str_5freduction_5fpred(s, v269, v290, v268, v245, v2, v244, v183, v182, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_58_eo__24str_5freduction_5fpred(s: &mut Store, v233: Term, v235: Term, v225: Term, v221: Term, v220: Term, v202: Term, v184: Term, v2: Term, v183: Term, v182: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v236 = match s.apply(v233, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v225, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v221, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Numeral(v239)) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v238, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v220, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v202, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v184, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v250, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo__24emb_5fVar, &[v252, v253]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v251, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.literal(Lit::Numeral(v256)) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v255, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v249, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v248, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.literal(Lit::Numeral(v261)) { Ok(v) => v, Err(e) => return Err(e) };
more_59_eo__24str_5freduction_5fpred(s, v260, v262, v247, v246, v2, v245, v244, v183, v182, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_57_eo__24str_5freduction_5fpred(s: &mut Store, v207: Term, v205: Term, v204: Term, v203: Term, v2: Term, v202: Term, v184: Term, v183: Term, v182: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v208 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo__24emb_5fVar, &[v208, v209]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v207, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.literal(Lit::Numeral(v212)) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v211, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v205, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v204, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.literal(Lit::Numeral(v217)) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v216, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v203, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match parse_int("10") { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::Numeral(v223)) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v222, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo__24emb_5fVar, &[v229, v230]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v228, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v226, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.literal(Lit::Numeral(v234)) { Ok(v) => v, Err(e) => return Err(e) };
more_58_eo__24str_5freduction_5fpred(s, v233, v235, v225, v221, v220, v202, v184, v2, v183, v182, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_56_eo__24str_5freduction_5fpred(s: &mut Store, v171: Term, v181: Term, v2: Term, v170: Term, v158: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v182 = match s.apply(v171, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v186, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo__24emb_5fVar, &[v189, v190]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v188, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.literal(Lit::Numeral(v194)) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v193, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.literal(Lit::Numeral(v197)) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v196, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v192, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v187, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v185, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v206, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_57_eo__24str_5freduction_5fpred(s, v207, v205, v204, v203, v2, v202, v184, v183, v182, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_55_eo__24str_5freduction_5fpred(s: &mut Store, v155: Term, v156: Term, v150: Term, v2: Term, v149: Term, v148: Term, v139: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v157 = match s.apply(v155, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v150, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo__24emb_5fVar, &[v162, v163]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v161, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Numeral(v166)) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v165, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v160, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v159, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__24emb_5fVar, &[v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v173, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v177, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v172, v180) { Ok(v) => v, Err(e) => return Err(e) };
more_56_eo__24str_5freduction_5fpred(s, v171, v181, v2, v170, v158, v149, v148, v139, v127, v113)
}
pub(super) fn more_54_eo__24str_5freduction_5fpred(s: &mut Store, v129: Term, v2: Term, v128: Term, v127: Term, v113: Term) -> CheckResult<Option<Term>> {
let v130 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Numeral(v130)) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v129, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.literal(Lit::Numeral(v135)) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v134, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v132, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v128, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v141, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Numeral(v145)) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v144, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v140, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo__24emb_5fVar, &[v152, v153]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v151, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_55_eo__24str_5freduction_5fpred(s, v155, v156, v150, v2, v149, v148, v139, v127, v113)
}
pub(super) fn more_53_eo__24str_5freduction_5fpred(s: &mut Store, v105: Term, v32: Term, v26: Term, v25: Term, v14: Term, v2: Term) -> CheckResult<Option<Term>> {
let v106 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v105, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v32, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v26, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v25, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v14, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v116, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v115, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo__40strings_5fstoi_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v121, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v122, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v120, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v114, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_54_eo__24str_5freduction_5fpred(s, v129, v2, v128, v127, v113)
}
pub(super) fn more_52_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v78: Term, v77: Term, v76: Term, v75: Term, v74: Term, v52: Term, v51: Term, v42: Term, v33: Term, v32: Term, v26: Term, v25: Term, v14: Term) -> CheckResult<Option<Term>> {
let v79 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(v84)) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v78, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v77, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(v89)) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v88, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v76, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match parse_int("10") { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(v93)) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v75, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v74, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v52, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v100, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v51, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v42, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v33, v104) { Ok(v) => v, Err(e) => return Err(e) };
more_53_eo__24str_5freduction_5fpred(s, v105, v32, v26, v25, v14, v2)
}
pub(super) fn more_51_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v51: Term, v42: Term, v33: Term, v32: Term, v26: Term, v25: Term, v14: Term) -> CheckResult<Option<Term>> {
let v52 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(v62)) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v56, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v55, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match parse_int("48") { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(v67)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v54, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(v71)) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v70, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v53, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_52_eo__24str_5freduction_5fpred(s, v2, v78, v77, v76, v75, v74, v52, v51, v42, v33, v32, v26, v25, v14)
}
pub(super) fn more_50_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v26: Term, v25: Term, v14: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v35, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(v39)) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v34, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__40strings_5fstoi_5fnon_5fdigit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v43, v50) { Ok(v) => v, Err(e) => return Err(e) };
more_51_eo__24str_5freduction_5fpred(s, v2, v51, v42, v33, v32, v26, v25, v14)
}
pub(super) fn case_5_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v16, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(v22)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v15, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24str_5freduction_5fpred(s, v2, v26, v25, v14)
}
pub(super) fn more_67_eo__24str_5freduction_5fpred(s: &mut Store, v153: Term, v160: Term, v151: Term, v147: Term, v112: Term, v111: Term, v96: Term, v25: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v153, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v151, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v147, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v112, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v164, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v111, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v96, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v25, v168) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v169))
}
pub(super) fn more_66_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v132: Term, v128: Term, v115: Term, v114: Term, v113: Term, v5: Term, v112: Term, v111: Term, v96: Term, v25: Term) -> CheckResult<Option<Term>> {
let v133 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Numeral(v136)) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v135, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Numeral(v139)) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v138, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v134, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v132, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v128, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v115, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v114, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v113, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v148, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Numeral(v155)) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v154, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Numeral(v158)) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v157, v159) { Ok(v) => v, Err(e) => return Err(e) };
more_67_eo__24str_5freduction_5fpred(s, v153, v160, v151, v147, v112, v111, v96, v25)
}
pub(super) fn more_65_eo__24str_5freduction_5fpred(s: &mut Store, v100: Term, v106: Term, v99: Term, v98: Term, v2: Term, v97: Term, v5: Term, v96: Term, v25: Term) -> CheckResult<Option<Term>> {
let v107 = match s.apply(v100, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v99, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v98, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v97, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v118, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(v121)) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v120, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::Numeral(v124)) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v123, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v119, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v117, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v129, v131) { Ok(v) => v, Err(e) => return Err(e) };
more_66_eo__24str_5freduction_5fpred(s, v2, v132, v128, v115, v114, v113, v5, v112, v111, v96, v25)
}
pub(super) fn more_64_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v80: Term, v47: Term, v38: Term, v28: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v81 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(v85)) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v84, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v82, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match eo__24eo_5ftypeof(s, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match eo__24eo_5fnil(s, v81, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v80, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v47, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v38, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v28, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v26, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Numeral(v103)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v102, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_65_eo__24str_5freduction_5fpred(s, v100, v106, v99, v98, v2, v97, v5, v96, v25)
}
pub(super) fn more_63_eo__24str_5freduction_5fpred(s: &mut Store, v52: Term, v2: Term, v51: Term, v5: Term, v49: Term, v48: Term, v47: Term, v38: Term, v28: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v52, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(v55)) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v54, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(v58)) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v53, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v51, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(v70)) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v69, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(v73)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v72, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v68, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v66, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v62, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v49, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v48, v79) { Ok(v) => v, Err(e) => return Err(e) };
more_64_eo__24str_5freduction_5fpred(s, v5, v2, v80, v47, v38, v28, v26, v25)
}
pub(super) fn more_62_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v5: Term, v2: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v30, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v29, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v40, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v39, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_63_eo__24str_5freduction_5fpred(s, v52, v2, v51, v5, v49, v48, v47, v38, v28, v26, v25)
}
pub(super) fn case_6_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(v11)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v15, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v14, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v7, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_62_eo__24str_5freduction_5fpred(s, v27, v5, v2, v26, v25)
}
pub(super) fn if_68_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v53 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(v55)) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v54, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v57, v62) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_69_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v78 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(v80)) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v79, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v82, v87) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v88)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_70_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v109 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(v111)) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v114, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v113, v118) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v119)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_71_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v170 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Numeral(v172)) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v171, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v175, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v174, v179) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v180)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_72_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v198 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v198, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::Numeral(v200)) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v199, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v203, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v206, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v202, v207) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v208)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_73_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v229 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.literal(Lit::Numeral(v231)) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v230, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v235, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v234, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v237, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v233, v238) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v239)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_74_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v289 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v289, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.literal(Lit::Numeral(v291)) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v290, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v295, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v294, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v297, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v293, v298) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v299)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_75_eo__24str_5freduction_5fpred(s: &mut Store, condition: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v313 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v313, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.literal(Lit::Numeral(v315)) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v314, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.apply(v319, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v318, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v317, v322) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v323)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_84_eo__24str_5freduction_5fpred(s: &mut Store, v304: Term, v326: Term, v303: Term, v302: Term, v282: Term, v281: Term, v266: Term, v146: Term, v28: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v327 = match s.apply(v304, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v303, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.apply(v302, v328) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v282, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v330, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v281, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v266, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v146, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v28, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v339, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v340, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v341, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v338, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v337, v343) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v344, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v336, v345) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v346))
}
pub(super) fn case_0_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(v4)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_0_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_1_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_2_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24is_5fseq_5fconst_5frec(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24is_5fseq_5fconst_5frec(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$is_seq_const_rec"
pub fn eo__24is_5fseq_5fconst_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(902), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fseq_5fconst_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(902), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24is_5fseq_5fconst_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$is_seq_const"
pub fn eo__24is_5fseq_5fconst(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24is_5fseq_5fconst(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24str_5fvalue_5flen(s: &mut Store, v2: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v2 != v3 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListLength, &[v4, a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
pub(super) fn if_1_eo__24str_5fvalue_5flen(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match eo__24is_5fseq_5fconst(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match requires_0_eo__24str_5fvalue_5flen(s, v2, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::IsStr, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_1_eo__24str_5fvalue_5flen(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fvalue_5flen(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fvalue_5flen(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_value_len"
pub fn eo__24str_5fvalue_5flen(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fvalue_5flen(s, a0);
s.leave();
result
}
pub(super) fn more_83_eo__24str_5freduction_5fpred(s: &mut Store, v268: Term, v278: Term, v5: Term, v267: Term, v2: Term, v8: Term, v266: Term, v146: Term, v28: Term) -> CheckResult<Option<Term>> {
let v279 = match s.apply(v268, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v279, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v267, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.literal(Lit::Numeral(v286)) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.builtin_core(EvalOp::IsEq, &[v285, v287]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match if_74_eo__24str_5freduction_5fpred(s, v288, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v284, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v283, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v305, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v306, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.literal(Lit::Numeral(v310)) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.builtin_core(EvalOp::IsEq, &[v309, v311]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match if_75_eo__24str_5freduction_5fpred(s, v312, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v308, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v307, v325) { Ok(v) => v, Err(e) => return Err(e) };
more_84_eo__24str_5freduction_5fpred(s, v304, v326, v303, v302, v282, v281, v266, v146, v28, v8, v5, v2)
}
pub(super) fn more_82_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v252: Term, v251: Term, v250: Term, v185: Term, v159: Term, v149: Term, v147: Term, v2: Term, v146: Term, v28: Term) -> CheckResult<Option<Term>> {
let v253 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v253, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Numeral(v255)) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v254, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v252, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match eo__24eo_5ftypeof(s, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match eo__24eo_5fnil(s, v251, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v250, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v185, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v159, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v149, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v147, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v271, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.literal(Lit::Numeral(v273)) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v272, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v275, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v270, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v269, v277) { Ok(v) => v, Err(e) => return Err(e) };
more_83_eo__24str_5freduction_5fpred(s, v268, v278, v5, v267, v2, v8, v266, v146, v28)
}
pub(super) fn more_81_eo__24str_5freduction_5fpred(s: &mut Store, v189: Term, v215: Term, v8: Term, v5: Term, v2: Term, v187: Term, v186: Term, v185: Term, v159: Term, v149: Term, v147: Term, v146: Term, v28: Term) -> CheckResult<Option<Term>> {
let v216 = match s.apply(v189, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v218, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v217, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v221, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.literal(Lit::Numeral(v226)) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.builtin_core(EvalOp::IsEq, &[v225, v227]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match if_73_eo__24str_5freduction_5fpred(s, v228, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v224, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v223, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.literal(Lit::Numeral(v243)) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.apply(v242, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v222, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v220, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v216, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v187, v248) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v186, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_82_eo__24str_5freduction_5fpred(s, v8, v5, v252, v251, v250, v185, v159, v149, v147, v2, v146, v28)
}
pub(super) fn more_80_eo__24str_5freduction_5fpred(s: &mut Store, v166: Term, v2: Term, v8: Term, v5: Term, v165: Term, v164: Term, v161: Term, v160: Term, v159: Term, v149: Term, v147: Term, v146: Term, v28: Term) -> CheckResult<Option<Term>> {
let v167 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.literal(Lit::Numeral(v167)) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.builtin_core(EvalOp::IsEq, &[v166, v168]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match if_71_eo__24str_5freduction_5fpred(s, v169, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v165, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v164, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v161, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v160, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v188, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Numeral(v195)) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.builtin_core(EvalOp::IsEq, &[v194, v196]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match if_72_eo__24str_5freduction_5fpred(s, v197, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v193, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v192, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.literal(Lit::Numeral(v212)) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v211, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v191, v214) { Ok(v) => v, Err(e) => return Err(e) };
more_81_eo__24str_5freduction_5fpred(s, v189, v215, v8, v5, v2, v187, v186, v185, v159, v149, v147, v146, v28)
}
pub(super) fn more_79_eo__24str_5freduction_5fpred(s: &mut Store, v130: Term, v141: Term, v65: Term, v47: Term, v37: Term, v29: Term, v8: Term, v5: Term, v2: Term, v28: Term) -> CheckResult<Option<Term>> {
let v142 = match s.apply(v130, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v65, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v47, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v37, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v29, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v148, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.literal(Lit::Numeral(v154)) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v153, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v156, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v151, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v150, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v163, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_80_eo__24str_5freduction_5fpred(s, v166, v2, v8, v5, v165, v164, v161, v160, v159, v149, v147, v146, v28)
}
pub(super) fn more_78_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v8: Term, v5: Term, v103: Term, v102: Term, v100: Term, v96: Term, v67: Term, v66: Term, v65: Term, v47: Term, v37: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v104 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(v106)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_core(EvalOp::IsEq, &[v105, v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match if_70_eo__24str_5freduction_5fpred(s, v108, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v104, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v103, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(v123)) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v122, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v102, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v100, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v96, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v67, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v66, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.literal(Lit::Numeral(v135)) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v134, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v132, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match eo__24eo_5ftypeof(s, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match eo__24eo_5fnil(s, v131, v140) { Ok(v) => v, Err(e) => return Err(e) };
more_79_eo__24str_5freduction_5fpred(s, v130, v141, v65, v47, v37, v29, v8, v5, v2, v28)
}
pub(super) fn more_77_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v66: Term, v65: Term, v47: Term, v37: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v67 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Numeral(v75)) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_core(EvalOp::IsEq, &[v74, v76]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match if_69_eo__24str_5freduction_5fpred(s, v77, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v73, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v72, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(v92)) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v71, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v69, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v97, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_78_eo__24str_5freduction_5fpred(s, v2, v8, v5, v103, v102, v100, v96, v67, v66, v65, v47, v37, v29, v28)
}
pub(super) fn more_76_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v31, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v30, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(v42)) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v39, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v38, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match eo__24str_5fvalue_5flen(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::IsEq, &[v49, v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match if_68_eo__24str_5freduction_5fpred(s, v52, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v48, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_77_eo__24str_5freduction_5fpred(s, v8, v5, v2, v66, v65, v47, v37, v29, v28)
}
pub(super) fn case_7_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(v14)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v10, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_76_eo__24str_5freduction_5fpred(s, v8, v5, v2, v29, v28)
}
pub(super) fn cases_0_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_4_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_97_eo__24str_5freduction_5fpred(s: &mut Store, v328: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v329 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v328, v329) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v111, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v93, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v80, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v54, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v36, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v26, v335) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v336))
}
pub(super) fn more_96_eo__24str_5freduction_5fpred(s: &mut Store, v302: Term, v303: Term, v301: Term, v298: Term, v295: Term, v5: Term, v294: Term, v275: Term, v274: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v304 = match s.construct(Constructor::eo__24emb_5fVar, &[v302, v303]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.apply(v301, v304) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v298, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v295, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v309, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v308, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.literal(Lit::Numeral(v312)) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v311, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v307, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v294, v315) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v275, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v317, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.apply(v274, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v167, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v147, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v322, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v146, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v133, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v121, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v112, v327) { Ok(v) => v, Err(e) => return Err(e) };
more_97_eo__24str_5freduction_5fpred(s, v328, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_95_eo__24str_5freduction_5fpred(s: &mut Store, v277: Term, v8: Term, v5: Term, v276: Term, v275: Term, v274: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v278 = match s.apply(v277, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v278, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo__24emb_5fVar, &[v281, v282]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v280, v283) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.literal(Lit::Numeral(v286)) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.apply(v285, v287) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::Numeral(v289)) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v288, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v284, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v279, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v276, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v296, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v297, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v299, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v300, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_96_eo__24str_5freduction_5fpred(s, v302, v303, v301, v298, v295, v5, v294, v275, v274, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_94_eo__24str_5freduction_5fpred(s: &mut Store, v253: Term, v252: Term, v249: Term, v246: Term, v8: Term, v5: Term, v245: Term, v235: Term, v234: Term, v214: Term, v212: Term, v178: Term, v168: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v254 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo__24emb_5fVar, &[v253, v254]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v252, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v249, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v246, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v259, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v260, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.construct(Constructor::eo__24emb_5fVar, &[v262, v263]) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v261, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v258, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v245, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match eo__24eo_5ftypeof(s, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match eo__24eo_5fnil(s, v235, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v234, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v214, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v212, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v178, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v168, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_95_eo__24str_5freduction_5fpred(s, v277, v8, v5, v276, v275, v274, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_93_eo__24str_5freduction_5fpred(s: &mut Store, v228: Term, v224: Term, v219: Term, v215: Term, v8: Term, v5: Term, v214: Term, v212: Term, v178: Term, v168: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v229 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.literal(Lit::Numeral(v229)) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v228, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v224, v231) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v219, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v215, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v236, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v238, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo__24emb_5fVar, &[v241, v242]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v240, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.apply(v237, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v247, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v250, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v251, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_94_eo__24str_5freduction_5fpred(s, v253, v252, v249, v246, v8, v5, v245, v235, v234, v214, v212, v178, v168, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_92_eo__24str_5freduction_5fpred(s: &mut Store, v203: Term, v8: Term, v5: Term, v202: Term, v189: Term, v179: Term, v2: Term, v178: Term, v168: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v204 = match s.apply(v203, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo__24emb_5fVar, &[v206, v207]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v205, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v202, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v189, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v179, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v213, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v216, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v217, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v218, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo__24emb_5fVar, &[v221, v222]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v220, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.literal(Lit::Numeral(v226)) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v225, v227) { Ok(v) => v, Err(e) => return Err(e) };
more_93_eo__24str_5freduction_5fpred(s, v228, v224, v219, v215, v8, v5, v214, v212, v178, v168, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_91_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v179: Term, v2: Term, v178: Term, v168: Term, v167: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v180 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v180, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v182, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__24emb_5fVar, &[v185, v186]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v184, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v181, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v191, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v192, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v194, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v195, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo__24emb_5fVar, &[v197, v198]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v196, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v193, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v190, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_92_eo__24str_5freduction_5fpred(s, v203, v8, v5, v202, v189, v179, v2, v178, v168, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_90_eo__24str_5freduction_5fpred(s: &mut Store, v154: Term, v8: Term, v5: Term, v153: Term, v150: Term, v149: Term, v148: Term, v2: Term, v147: Term, v146: Term, v133: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v155 = match s.apply(v154, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo__24emb_5fVar, &[v157, v158]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v156, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v153, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v150, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.literal(Lit::Numeral(v163)) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v162, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v149, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v148, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v172, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__24emb_5fVar, &[v174, v175]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v173, v176) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v169, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_91_eo__24str_5freduction_5fpred(s, v8, v5, v179, v2, v178, v168, v167, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_89_eo__24str_5freduction_5fpred(s: &mut Store, v128: Term, v130: Term, v123: Term, v122: Term, v8: Term, v5: Term, v2: Term, v121: Term, v112: Term, v111: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v131 = match s.apply(v128, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v123, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v122, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo__24emb_5fVar, &[v137, v138]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v136, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v140, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v135, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v134, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v151, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_90_eo__24str_5freduction_5fpred(s, v154, v8, v5, v153, v150, v149, v148, v2, v147, v146, v133, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_88_eo__24str_5freduction_5fpred(s: &mut Store, v101: Term, v104: Term, v98: Term, v95: Term, v94: Term, v8: Term, v5: Term, v2: Term, v93: Term, v80: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v105 = match s.apply(v101, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v98, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v95, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Numeral(v108)) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v94, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo__24emb_5fVar, &[v115, v116]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v114, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v118, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v113, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__24emb_5fVar, &[v125, v126]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v124, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Numeral(v129)) { Ok(v) => v, Err(e) => return Err(e) };
more_89_eo__24str_5freduction_5fpred(s, v128, v130, v123, v122, v8, v5, v2, v121, v112, v111, v93, v80, v54, v36, v26)
}
pub(super) fn more_87_eo__24str_5freduction_5fpred(s: &mut Store, v65: Term, v78: Term, v55: Term, v8: Term, v5: Term, v2: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v79 = match s.apply(v65, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v55, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(v86)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v85, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v82, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Numeral(v90)) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v89, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v81, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v103, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_88_eo__24str_5freduction_5fpred(s, v101, v104, v98, v95, v94, v8, v5, v2, v93, v80, v54, v36, v26)
}
pub(super) fn more_86_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v54: Term, v36: Term, v26: Term) -> CheckResult<Option<Term>> {
let v55 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v60, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v56, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__40strings_5foccur_5findex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v72, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v70, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v67, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
more_87_eo__24str_5freduction_5fpred(s, v65, v78, v55, v8, v5, v2, v54, v36, v26)
}
pub(super) fn more_85_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v28: Term, v27: Term, v2: Term, v26: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__40strings_5fnum_5foccur, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(v33)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v32, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v27, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v38, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40strings_5freplace_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(v50)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v45, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v37, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_86_eo__24str_5freduction_5fpred(s, v8, v5, v2, v54, v36, v26)
}
pub(super) fn case_8_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24seq_5fempty(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_85_eo__24str_5freduction_5fpred(s, v8, v5, v28, v27, v2, v26)
}
pub(super) fn more_111_eo__24str_5freduction_5fpred(s: &mut Store, v55: Term, v367: Term, v32: Term) -> CheckResult<Option<Term>> {
let v368 = match s.apply(v55, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.apply(v32, v368) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v369))
}
pub(super) fn more_110_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v342: Term, v5: Term, v341: Term, v332: Term, v331: Term, v330: Term, v328: Term, v312: Term, v304: Term, v303: Term, v271: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v343 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v343, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v342, v344) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v346, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.apply(v347, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.literal(Lit::Numeral(v349)) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v348, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v345, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.apply(v341, v352) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.apply(v332, v353) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.apply(v331, v354) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v355, v356) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.apply(v330, v357) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v328, v358) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v312, v359) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v304, v360) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.apply(v361, v362) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.apply(v303, v363) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.apply(v271, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.apply(v161, v365) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v134, v366) { Ok(v) => v, Err(e) => return Err(e) };
more_111_eo__24str_5freduction_5fpred(s, v55, v367, v32)
}
pub(super) fn more_109_eo__24str_5freduction_5fpred(s: &mut Store, v315: Term, v8: Term, v5: Term, v314: Term, v313: Term, v2: Term, v312: Term, v304: Term, v303: Term, v271: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v316 = match s.apply(v315, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.literal(Lit::Numeral(v317)) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v316, v318) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v320, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.literal(Lit::Numeral(v323)) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v322, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v319, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v314, v326) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v313, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v329, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v333, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v335, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v336, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.literal(Lit::Numeral(v338)) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v337, v339) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v334, v340) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_110_eo__24str_5freduction_5fpred(s, v8, v342, v5, v341, v332, v331, v330, v328, v312, v304, v303, v271, v161, v134, v55, v32)
}
pub(super) fn more_108_eo__24str_5freduction_5fpred(s: &mut Store, v284: Term, v290: Term, v8: Term, v5: Term, v283: Term, v274: Term, v273: Term, v272: Term, v2: Term, v271: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v291 = match s.apply(v284, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v292, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.apply(v293, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.literal(Lit::Numeral(v295)) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v294, v296) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v291, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.apply(v283, v298) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.apply(v274, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.apply(v273, v300) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v301, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v272, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.apply(v307, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.apply(v308, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.apply(v309, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.apply(v306, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.apply(v305, v311) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_109_eo__24str_5freduction_5fpred(s, v315, v8, v5, v314, v313, v2, v312, v304, v303, v271, v161, v134, v55, v32)
}
pub(super) fn more_107_eo__24str_5freduction_5fpred(s: &mut Store, v223: Term, v264: Term, v222: Term, v183: Term, v171: Term, v162: Term, v8: Term, v5: Term, v2: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v265 = match s.apply(v223, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v265, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v222, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v183, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v171, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v162, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v275, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v277, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v278, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.literal(Lit::Numeral(v280)) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.apply(v279, v281) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.apply(v276, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v286, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.literal(Lit::Numeral(v288)) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.apply(v287, v289) { Ok(v) => v, Err(e) => return Err(e) };
more_108_eo__24str_5freduction_5fpred(s, v284, v290, v8, v5, v283, v274, v273, v272, v2, v271, v161, v134, v55, v32)
}
pub(super) fn more_106_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v237: Term, v236: Term, v227: Term, v226: Term, v225: Term, v224: Term, v223: Term, v222: Term, v183: Term, v171: Term, v162: Term, v2: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v238 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v238, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Numeral(v241)) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v240, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v237, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v245, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v246, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(v248)) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v247, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v244, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v236, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v227, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v226, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Numeral(v255)) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v254, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.construct(Constructor::eo__24emb_5fVar, &[v258, v259]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v257, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v225, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v262, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v224, v263) { Ok(v) => v, Err(e) => return Err(e) };
more_107_eo__24str_5freduction_5fpred(s, v223, v264, v222, v183, v171, v162, v8, v5, v2, v161, v134, v55, v32)
}
pub(super) fn more_105_eo__24str_5freduction_5fpred(s: &mut Store, v211: Term, v5: Term, v209: Term, v201: Term, v192: Term, v191: Term, v190: Term, v185: Term, v184: Term, v8: Term, v183: Term, v171: Term, v162: Term, v2: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v212 = match s.apply(v211, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.literal(Lit::Numeral(v213)) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v212, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v209, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v201, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v192, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v191, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v190, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v185, v220) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.apply(v184, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v228, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v231, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.literal(Lit::Numeral(v233)) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v232, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v229, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_106_eo__24str_5freduction_5fpred(s, v8, v5, v237, v236, v227, v226, v225, v224, v223, v222, v183, v171, v162, v2, v161, v134, v55, v32)
}
pub(super) fn more_104_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v185: Term, v184: Term, v183: Term, v171: Term, v162: Term, v2: Term, v161: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v186 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo__24emb_5fVar, &[v187, v188]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v186, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v193, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v195, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v196, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.literal(Lit::Numeral(v198)) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v197, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v194, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v203, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.literal(Lit::Numeral(v206)) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v205, v207) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v202, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v210, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_105_eo__24str_5freduction_5fpred(s, v211, v5, v209, v201, v192, v191, v190, v185, v184, v8, v183, v171, v162, v2, v161, v134, v55, v32)
}
pub(super) fn more_103_eo__24str_5freduction_5fpred(s: &mut Store, v135: Term, v160: Term, v8: Term, v5: Term, v2: Term, v134: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v135, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__24emb_5fVar, &[v165, v166]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v164, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v168, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v163, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo__24emb_5fVar, &[v175, v176]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v174, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.literal(Lit::Numeral(v179)) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v178, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v173, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v172, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_104_eo__24str_5freduction_5fpred(s, v8, v5, v185, v184, v183, v171, v162, v2, v161, v134, v55, v32)
}
pub(super) fn more_102_eo__24str_5freduction_5fpred(s: &mut Store, v56: Term, v133: Term, v8: Term, v5: Term, v2: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v134 = match s.apply(v56, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Numeral(v141)) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v140, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Numeral(v147)) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v143, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v138, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v137, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v136, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v154, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.literal(Lit::Numeral(v157)) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v156, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v153, v159) { Ok(v) => v, Err(e) => return Err(e) };
more_103_eo__24str_5freduction_5fpred(s, v135, v160, v8, v5, v2, v134, v55, v32)
}
pub(super) fn more_101_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v107: Term, v105: Term, v104: Term, v103: Term, v74: Term, v58: Term, v56: Term, v2: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v108 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Numeral(v111)) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v110, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v107, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v115, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v119, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v121, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v118, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v114, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v105, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v104, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v128, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v103, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v74, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v58, v132) { Ok(v) => v, Err(e) => return Err(e) };
more_102_eo__24str_5freduction_5fpred(s, v56, v133, v8, v5, v2, v55, v32)
}
pub(super) fn more_100_eo__24str_5freduction_5fpred(s: &mut Store, v80: Term, v5: Term, v78: Term, v8: Term, v76: Term, v75: Term, v74: Term, v58: Term, v56: Term, v2: Term, v55: Term, v32: Term) -> CheckResult<Option<Term>> {
let v81 = match s.apply(v80, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(v82)) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v81, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v78, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Numeral(v90)) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v89, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v86, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(v97)) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v96, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v93, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v85, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v76, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v75, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_101_eo__24str_5freduction_5fpred(s, v8, v5, v107, v105, v104, v103, v74, v58, v56, v2, v55, v32)
}
pub(super) fn more_99_eo__24str_5freduction_5fpred(s: &mut Store, v45: Term, v54: Term, v8: Term, v5: Term, v2: Term, v32: Term) -> CheckResult<Option<Term>> {
let v55 = match s.apply(v45, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Numeral(v63)) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v65, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v60, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v59, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_100_eo__24str_5freduction_5fpred(s, v80, v5, v78, v8, v76, v75, v74, v58, v56, v2, v55, v32)
}
pub(super) fn more_98_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v28: Term, v25: Term, v23: Term, v15: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v23, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v15, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(v38)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v37, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v34, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(v42)) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v33, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v47, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_99_eo__24str_5freduction_5fpred(s, v45, v54, v8, v5, v2, v32)
}
pub(super) fn case_9_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v16, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_98_eo__24str_5freduction_5fpred(s, v27, v28, v25, v23, v15, v8, v5, v2)
}
pub(super) fn more_130_eo__24str_5freduction_5fpred(s: &mut Store, v172: Term, v479: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v480 = match s.apply(v172, v479) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match s.apply(v159, v480) { Ok(v) => v, Err(e) => return Err(e) };
let v482 = match s.apply(v147, v481) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match s.apply(v138, v482) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match s.apply(v483, v484) { Ok(v) => v, Err(e) => return Err(e) };
let v486 = match s.apply(v137, v485) { Ok(v) => v, Err(e) => return Err(e) };
let v487 = match s.apply(v105, v486) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match s.apply(v92, v487) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match s.apply(v66, v488) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match s.apply(v48, v489) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match s.apply(v38, v490) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v491))
}
pub(super) fn more_129_eo__24str_5freduction_5fpred(s: &mut Store, v452: Term, v453: Term, v451: Term, v450: Term, v446: Term, v445: Term, v443: Term, v403: Term, v393: Term, v392: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v454 = match s.construct(Constructor::eo__24emb_5fVar, &[v452, v453]) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match s.apply(v451, v454) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.literal(Lit::Numeral(v457)) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.apply(v456, v458) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.literal(Lit::Numeral(v460)) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.apply(v459, v461) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match s.apply(v455, v462) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.apply(v450, v463) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.apply(v446, v464) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.apply(v465, v466) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match s.apply(v445, v467) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.apply(v443, v468) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.apply(v403, v469) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match s.apply(v393, v470) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.apply(v471, v472) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match s.apply(v392, v473) { Ok(v) => v, Err(e) => return Err(e) };
let v475 = match s.apply(v286, v474) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.apply(v217, v475) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match s.apply(v173, v476) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match s.apply(v477, v478) { Ok(v) => v, Err(e) => return Err(e) };
more_130_eo__24str_5freduction_5fpred(s, v172, v479, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_128_eo__24str_5freduction_5fpred(s: &mut Store, v428: Term, v429: Term, v427: Term, v424: Term, v415: Term, v8: Term, v5: Term, v414: Term, v404: Term, v2: Term, v403: Term, v393: Term, v392: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v430 = match s.construct(Constructor::eo__24emb_5fVar, &[v428, v429]) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match s.apply(v427, v430) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.apply(v424, v431) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.apply(v415, v432) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match s.apply(v434, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.apply(v435, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.construct(Constructor::eo__24emb_5fVar, &[v437, v438]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.apply(v436, v439) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.apply(v433, v440) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match s.apply(v414, v441) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.apply(v404, v442) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.apply(v444, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match s.apply(v447, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.apply(v448, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match s.apply(v449, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_129_eo__24str_5freduction_5fpred(s, v452, v453, v451, v450, v446, v445, v443, v403, v393, v392, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_127_eo__24str_5freduction_5fpred(s: &mut Store, v405: Term, v8: Term, v5: Term, v404: Term, v2: Term, v403: Term, v393: Term, v392: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v406 = match s.apply(v405, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.apply(v407, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.apply(v408, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.construct(Constructor::eo__24emb_5fVar, &[v410, v411]) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.apply(v409, v412) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v406, v413) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.apply(v416, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v418, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.apply(v420, v421) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.apply(v419, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.apply(v417, v423) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v425, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.apply(v426, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_128_eo__24str_5freduction_5fpred(s, v428, v429, v427, v424, v415, v8, v5, v414, v404, v2, v403, v393, v392, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_126_eo__24str_5freduction_5fpred(s: &mut Store, v378: Term, v381: Term, v358: Term, v5: Term, v357: Term, v356: Term, v355: Term, v308: Term, v296: Term, v287: Term, v8: Term, v2: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v382 = match s.apply(v378, v381) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.apply(v358, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.apply(v383, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.apply(v357, v384) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.apply(v356, v385) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.apply(v386, v387) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.apply(v355, v388) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.apply(v308, v389) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.apply(v296, v390) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.apply(v287, v391) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v395, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v396, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v397, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.construct(Constructor::eo__24emb_5fVar, &[v399, v400]) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v398, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.apply(v394, v402) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_127_eo__24str_5freduction_5fpred(s, v405, v8, v5, v404, v2, v403, v393, v392, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_125_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v357: Term, v356: Term, v355: Term, v308: Term, v296: Term, v287: Term, v2: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v358 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.apply(v359, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v361, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.apply(v363, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v365, v366) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.apply(v364, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.apply(v362, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v370, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.apply(v371, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.construct(Constructor::eo__24emb_5fVar, &[v373, v374]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.apply(v372, v375) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.apply(v369, v376) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.apply(v360, v377) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.construct(Constructor::eo__24emb_5fVar, &[v379, v380]) { Ok(v) => v, Err(e) => return Err(e) };
more_126_eo__24str_5freduction_5fpred(s, v378, v381, v358, v5, v357, v356, v355, v308, v296, v287, v8, v2, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_124_eo__24str_5freduction_5fpred(s: &mut Store, v316: Term, v333: Term, v8: Term, v5: Term, v315: Term, v310: Term, v309: Term, v308: Term, v296: Term, v287: Term, v2: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v334 = match s.apply(v316, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v335, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v337, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v339, v340) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v338, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v336, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v344, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v345, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.construct(Constructor::eo__24emb_5fVar, &[v347, v348]) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v346, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v343, v350) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v334, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.apply(v315, v352) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.apply(v310, v353) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.apply(v309, v354) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_125_eo__24str_5freduction_5fpred(s, v8, v5, v357, v356, v355, v308, v296, v287, v2, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_123_eo__24str_5freduction_5fpred(s: &mut Store, v297: Term, v307: Term, v8: Term, v5: Term, v296: Term, v287: Term, v2: Term, v286: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v308 = match s.apply(v297, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.construct(Constructor::eo__24emb_5fVar, &[v312, v313]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v311, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.apply(v317, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v318, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo__24emb_5fVar, &[v321, v322]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v320, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.literal(Lit::Numeral(v326)) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v325, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.literal(Lit::Numeral(v329)) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v328, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v324, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v319, v332) { Ok(v) => v, Err(e) => return Err(e) };
more_124_eo__24str_5freduction_5fpred(s, v316, v333, v8, v5, v315, v310, v309, v308, v296, v287, v2, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_122_eo__24str_5freduction_5fpred(s: &mut Store, v281: Term, v282: Term, v280: Term, v278: Term, v218: Term, v8: Term, v5: Term, v2: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v283 = match s.apply(v281, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.apply(v280, v283) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.apply(v278, v284) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v218, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.construct(Constructor::eo__24emb_5fVar, &[v290, v291]) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v289, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.apply(v293, v294) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.apply(v288, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.construct(Constructor::eo__24emb_5fVar, &[v300, v301]) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v299, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.literal(Lit::Numeral(v304)) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v303, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v298, v306) { Ok(v) => v, Err(e) => return Err(e) };
more_123_eo__24str_5freduction_5fpred(s, v297, v307, v8, v5, v296, v287, v2, v286, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_121_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v258: Term, v239: Term, v219: Term, v218: Term, v2: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v259 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v259, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v261, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v263, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v262, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v260, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v268, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v269, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo__24emb_5fVar, &[v271, v272]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v270, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v267, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v258, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v239, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v219, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v279, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_122_eo__24str_5freduction_5fpred(s, v281, v282, v280, v278, v218, v8, v5, v2, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_120_eo__24str_5freduction_5fpred(s: &mut Store, v232: Term, v5: Term, v230: Term, v221: Term, v8: Term, v219: Term, v218: Term, v2: Term, v217: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v233 = match s.apply(v232, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo__24emb_5fVar, &[v234, v235]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v233, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v230, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v221, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v241, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v242, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo__24emb_5fVar, &[v245, v246]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v244, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.literal(Lit::Numeral(v250)) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v249, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.literal(Lit::Numeral(v253)) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v252, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v248, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v243, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v240, v257) { Ok(v) => v, Err(e) => return Err(e) };
more_121_eo__24str_5freduction_5fpred(s, v8, v5, v258, v239, v219, v218, v2, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_119_eo__24str_5freduction_5fpred(s: &mut Store, v207: Term, v206: Term, v203: Term, v194: Term, v175: Term, v174: Term, v8: Term, v5: Term, v2: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v208 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo__24emb_5fVar, &[v207, v208]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.apply(v206, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v203, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v194, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v175, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Numeral(v214)) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v213, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v174, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.apply(v220, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v222, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v224, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v226, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v225, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v223, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v231, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_120_eo__24str_5freduction_5fpred(s, v232, v5, v230, v221, v8, v219, v218, v2, v217, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_118_eo__24str_5freduction_5fpred(s: &mut Store, v181: Term, v180: Term, v179: Term, v176: Term, v8: Term, v5: Term, v175: Term, v174: Term, v2: Term, v173: Term, v172: Term, v159: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v182 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo__24emb_5fVar, &[v181, v182]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v180, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.literal(Lit::Numeral(v186)) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v185, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.literal(Lit::Numeral(v189)) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v184, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v179, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v176, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v195, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.apply(v197, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v199, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v198, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.apply(v196, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v204, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v205, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_119_eo__24str_5freduction_5fpred(s, v207, v206, v203, v194, v175, v174, v8, v5, v2, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_117_eo__24str_5freduction_5fpred(s: &mut Store, v149: Term, v157: Term, v148: Term, v8: Term, v5: Term, v2: Term, v147: Term, v138: Term, v137: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v158 = match s.apply(v149, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v148, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo__24emb_5fVar, &[v163, v164]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v162, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v166, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v161, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v160, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v177, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_118_eo__24str_5freduction_5fpred(s, v181, v180, v179, v176, v8, v5, v175, v174, v2, v173, v172, v159, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_116_eo__24str_5freduction_5fpred(s: &mut Store, v129: Term, v131: Term, v107: Term, v106: Term, v8: Term, v5: Term, v2: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v132 = match s.apply(v129, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v107, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Numeral(v134)) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v133, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v106, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo__24emb_5fVar, &[v141, v142]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v140, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v144, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v139, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo__24emb_5fVar, &[v151, v152]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v150, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Numeral(v155)) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v154, v156) { Ok(v) => v, Err(e) => return Err(e) };
more_117_eo__24str_5freduction_5fpred(s, v149, v157, v148, v8, v5, v2, v147, v138, v137, v105, v92, v66, v48, v38)
}
pub(super) fn more_115_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v106: Term, v2: Term, v105: Term, v92: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v107 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v112, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v113, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v110, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v119, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v118, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v108, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v125, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v124, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v122, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Numeral(v130)) { Ok(v) => v, Err(e) => return Err(e) };
more_116_eo__24str_5freduction_5fpred(s, v129, v131, v107, v106, v8, v5, v2, v105, v92, v66, v48, v38)
}
pub(super) fn more_114_eo__24str_5freduction_5fpred(s: &mut Store, v80: Term, v8: Term, v5: Term, v79: Term, v77: Term, v67: Term, v2: Term, v66: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v81 = match s.apply(v80, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v82, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v79, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v77, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v67, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Numeral(v98)) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v97, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v94, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(v102)) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v101, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v93, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_115_eo__24str_5freduction_5fpred(s, v8, v5, v106, v2, v105, v92, v66, v48, v38)
}
pub(super) fn more_113_eo__24str_5freduction_5fpred(s: &mut Store, v51: Term, v55: Term, v50: Term, v8: Term, v5: Term, v2: Term, v49: Term, v48: Term, v38: Term) -> CheckResult<Option<Term>> {
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v50, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(v62)) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v57, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v49, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v72, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v68, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_114_eo__24str_5freduction_5fpred(s, v80, v8, v5, v79, v77, v67, v2, v66, v48, v38)
}
pub(super) fn more_112_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v30: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v28, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(v45)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v39, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_113_eo__24str_5freduction_5fpred(s, v51, v55, v50, v8, v5, v2, v49, v48, v38)
}
pub(super) fn case_10_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v13, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(v21)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v11, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(v25)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v10, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_112_eo__24str_5freduction_5fpred(s, v8, v5, v2, v30, v29, v28)
}
pub(super) fn more_141_eo__24str_5freduction_5fpred(s: &mut Store, v171: Term, v274: Term, v170: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v275 = match s.apply(v171, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.apply(v275, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.apply(v170, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v56, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v40, v279) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v280))
}
pub(super) fn more_140_eo__24str_5freduction_5fpred(s: &mut Store, v246: Term, v250: Term, v245: Term, v243: Term, v5: Term, v242: Term, v241: Term, v240: Term, v219: Term, v207: Term, v198: Term, v197: Term, v196: Term, v185: Term, v184: Term, v171: Term, v170: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v251 = match s.apply(v246, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v245, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo__24emb_5fVar, &[v253, v254]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v252, v255) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v243, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v257, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v242, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v241, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v260, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v240, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v219, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v207, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v198, v265) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v197, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v267, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v196, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v185, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v271, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v184, v273) { Ok(v) => v, Err(e) => return Err(e) };
more_141_eo__24str_5freduction_5fpred(s, v171, v274, v170, v56, v40)
}
pub(super) fn more_139_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v226: Term, v221: Term, v220: Term, v219: Term, v207: Term, v198: Term, v197: Term, v196: Term, v185: Term, v184: Term, v171: Term, v170: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v227 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v228, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v227, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.apply(v232, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v233, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v234, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v231, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v230, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v226, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v221, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v220, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.apply(v244, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v247, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v248, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v249, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_140_eo__24str_5freduction_5fpred(s, v246, v250, v245, v243, v5, v242, v241, v240, v219, v207, v198, v197, v196, v185, v184, v171, v170, v56, v40)
}
pub(super) fn more_138_eo__24str_5freduction_5fpred(s: &mut Store, v201: Term, v200: Term, v199: Term, v8: Term, v5: Term, v2: Term, v198: Term, v197: Term, v196: Term, v185: Term, v184: Term, v171: Term, v170: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v202 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo__24emb_5fVar, &[v201, v202]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v200, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.apply(v204, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.apply(v199, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.construct(Constructor::eo__24emb_5fVar, &[v211, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v210, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.literal(Lit::Numeral(v215)) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v214, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v209, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v208, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo__24emb_5fVar, &[v223, v224]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v222, v225) { Ok(v) => v, Err(e) => return Err(e) };
more_139_eo__24str_5freduction_5fpred(s, v8, v5, v2, v226, v221, v220, v219, v207, v198, v197, v196, v185, v184, v171, v170, v56, v40)
}
pub(super) fn more_137_eo__24str_5freduction_5fpred(s: &mut Store, v176: Term, v5: Term, v2: Term, v174: Term, v173: Term, v172: Term, v8: Term, v171: Term, v170: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v177 = match s.apply(v176, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v177, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v174, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v173, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.literal(Lit::Numeral(v181)) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v180, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v172, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v190, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v191, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.apply(v188, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v187, v193) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v194, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v186, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_138_eo__24str_5freduction_5fpred(s, v201, v200, v199, v8, v5, v2, v198, v197, v196, v185, v184, v171, v170, v56, v40)
}
pub(super) fn more_136_eo__24str_5freduction_5fpred(s: &mut Store, v151: Term, v152: Term, v150: Term, v148: Term, v5: Term, v147: Term, v146: Term, v145: Term, v127: Term, v115: Term, v82: Term, v72: Term, v57: Term, v8: Term, v2: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v153 = match s.construct(Constructor::eo__24emb_5fVar, &[v151, v152]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v150, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo__24emb_5fVar, &[v155, v156]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v154, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v148, v158) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v159, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v147, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v146, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v162, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v145, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v127, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v115, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v82, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v72, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v57, v169) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v175, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_137_eo__24str_5freduction_5fpred(s, v176, v5, v2, v174, v173, v172, v8, v171, v170, v56, v40)
}
pub(super) fn more_135_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v128: Term, v5: Term, v127: Term, v115: Term, v82: Term, v72: Term, v57: Term, v2: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v129 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo__24emb_5fVar, &[v131, v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v130, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v136, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v135, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__24emb_5fVar, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v138, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v134, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v129, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v128, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_136_eo__24str_5freduction_5fpred(s, v151, v152, v150, v148, v5, v147, v146, v145, v127, v115, v82, v72, v57, v8, v2, v56, v40)
}
pub(super) fn more_134_eo__24str_5freduction_5fpred(s: &mut Store, v103: Term, v8: Term, v102: Term, v5: Term, v2: Term, v89: Term, v84: Term, v83: Term, v82: Term, v72: Term, v57: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v104 = match s.apply(v103, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v102, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v106, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v105, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v89, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v84, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v83, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo__24emb_5fVar, &[v119, v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v118, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(v123)) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v122, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v117, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v116, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_135_eo__24str_5freduction_5fpred(s, v8, v128, v5, v127, v115, v82, v72, v57, v2, v56, v40)
}
pub(super) fn more_133_eo__24str_5freduction_5fpred(s: &mut Store, v75: Term, v78: Term, v2: Term, v74: Term, v73: Term, v8: Term, v5: Term, v72: Term, v57: Term, v56: Term, v40: Term) -> CheckResult<Option<Term>> {
let v79 = match s.apply(v75, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v74, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v73, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__24emb_5fVar, &[v86, v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v85, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v92, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v91, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Numeral(v99)) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v90, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_134_eo__24str_5freduction_5fpred(s, v103, v8, v102, v5, v2, v89, v84, v83, v82, v72, v57, v56, v40)
}
pub(super) fn more_132_eo__24str_5freduction_5fpred(s: &mut Store, v54: Term, v2: Term, v46: Term, v8: Term, v5: Term, v40: Term) -> CheckResult<Option<Term>> {
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v46, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__24emb_5fVar, &[v60, v61]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v59, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__24emb_5fVar, &[v65, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v64, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v63, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v58, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__24emb_5fVar, &[v76, v77]) { Ok(v) => v, Err(e) => return Err(e) };
more_133_eo__24str_5freduction_5fpred(s, v75, v78, v2, v74, v73, v8, v5, v72, v57, v56, v40)
}
pub(super) fn more_131_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v29: Term, v28: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match parse_int("-1") { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(v37)) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v28, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::String(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v42, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v41, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v47, v53) { Ok(v) => v, Err(e) => return Err(e) };
more_132_eo__24str_5freduction_5fpred(s, v54, v2, v46, v8, v5, v40)
}
pub(super) fn case_11_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(v20)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v17, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v10, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_131_eo__24str_5freduction_5fpred(s, v8, v5, v2, v29, v28)
}
pub(super) fn more_147_eo__24str_5freduction_5fpred(s: &mut Store, v51: Term, v153: Term, v39: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v154 = match s.apply(v51, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v39, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v27, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v18, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v17, v157) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v158))
}
pub(super) fn more_146_eo__24str_5freduction_5fpred(s: &mut Store, v127: Term, v126: Term, v124: Term, v123: Term, v5: Term, v122: Term, v89: Term, v88: Term, v63: Term, v51: Term, v39: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v128 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__24emb_5fVar, &[v127, v128]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v126, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v124, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v123, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__24emb_5fVar, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v138, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v136, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v135, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v122, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v89, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v149, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v88, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v63, v152) { Ok(v) => v, Err(e) => return Err(e) };
more_147_eo__24str_5freduction_5fpred(s, v51, v153, v39, v27, v18, v17)
}
pub(super) fn more_145_eo__24str_5freduction_5fpred(s: &mut Store, v101: Term, v100: Term, v98: Term, v97: Term, v2: Term, v96: Term, v5: Term, v89: Term, v88: Term, v63: Term, v51: Term, v39: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v102 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__24emb_5fVar, &[v101, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v100, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(v105)) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v104, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v98, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v97, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__24emb_5fVar, &[v113, v114]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v112, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(v117)) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v116, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v110, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v109, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v96, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_146_eo__24str_5freduction_5fpred(s, v127, v126, v124, v123, v5, v122, v89, v88, v63, v51, v39, v27, v18, v17)
}
pub(super) fn more_144_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v76: Term, v65: Term, v64: Term, v5: Term, v63: Term, v51: Term, v39: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.literal(Lit::Numeral(v79)) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo__24emb_5fVar, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v81, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v76, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v65, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v64, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v91, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v90, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_145_eo__24str_5freduction_5fpred(s, v101, v100, v98, v97, v2, v96, v5, v89, v88, v63, v51, v39, v27, v18, v17)
}
pub(super) fn more_143_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v5: Term, v51: Term, v39: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v52 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24emb_5fVar, &[v55, v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v54, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v53, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v52, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(v69)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo__24emb_5fVar, &[v72, v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v71, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v66, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_144_eo__24str_5freduction_5fpred(s, v2, v76, v65, v64, v5, v63, v51, v39, v27, v18, v17)
}
pub(super) fn more_142_eo__24str_5freduction_5fpred(s: &mut Store, v19: Term, v26: Term, v5: Term, v2: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24emb_5fVar, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(v35)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v29, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v28, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__24emb_5fVar, &[v43, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v42, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v41, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v40, v50) { Ok(v) => v, Err(e) => return Err(e) };
more_143_eo__24str_5freduction_5fpred(s, v2, v5, v51, v39, v27, v18, v17)
}
pub(super) fn case_12_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v12, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fVar, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_142_eo__24str_5freduction_5fpred(s, v19, v26, v5, v2, v18, v17)
}
pub(super) fn more_153_eo__24str_5freduction_5fpred(s: &mut Store, v17: Term, v154: Term, v16: Term) -> CheckResult<Option<Term>> {
let v155 = match s.apply(v17, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v155, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v16, v157) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v158))
}
pub(super) fn more_152_eo__24str_5freduction_5fpred(s: &mut Store, v127: Term, v126: Term, v113: Term, v2: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v128 = match parse_int("32") { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(v128)) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v127, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v126, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v113, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__24emb_5fVar, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v138, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v136, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v135, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v72, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v55, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v149, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v54, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v38, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v26, v153) { Ok(v) => v, Err(e) => return Err(e) };
more_153_eo__24str_5freduction_5fpred(s, v17, v154, v16)
}
pub(super) fn more_151_eo__24str_5freduction_5fpred(s: &mut Store, v100: Term, v94: Term, v93: Term, v92: Term, v91: Term, v73: Term, v2: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v101 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(v101)) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v94, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v93, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match parse_int("90") { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(v106)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v92, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v91, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v73, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__24emb_5fVar, &[v118, v119]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v117, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v121, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v115, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v114, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_152_eo__24str_5freduction_5fpred(s, v127, v126, v113, v2, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_150_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v74: Term, v73: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("65") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo__24emb_5fVar, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v81, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(v86)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v85, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v79, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v78, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v74, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__24emb_5fVar, &[v97, v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v96, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_151_eo__24str_5freduction_5fpred(s, v100, v94, v93, v92, v91, v73, v2, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_149_eo__24str_5freduction_5fpred(s: &mut Store, v47: Term, v49: Term, v46: Term, v45: Term, v40: Term, v39: Term, v2: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v45, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v40, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v39, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v58, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__24emb_5fVar, &[v64, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v63, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(v68)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v57, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v56, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_150_eo__24str_5freduction_5fpred(s, v2, v74, v73, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_148_eo__24str_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v18: Term, v2: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v28, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v27, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__24emb_5fVar, &[v42, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_149_eo__24str_5freduction_5fpred(s, v47, v49, v46, v45, v40, v39, v2, v38, v26, v17, v16)
}
pub(super) fn case_13_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fVar, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_148_eo__24str_5freduction_5fpred(s, v23, v24, v18, v2, v17, v16)
}
pub(super) fn more_159_eo__24str_5freduction_5fpred(s: &mut Store, v17: Term, v154: Term, v16: Term) -> CheckResult<Option<Term>> {
let v155 = match s.apply(v17, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v155, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v16, v157) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v158))
}
pub(super) fn more_158_eo__24str_5freduction_5fpred(s: &mut Store, v127: Term, v126: Term, v113: Term, v2: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v128 = match parse_int("-32") { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(v128)) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v127, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Numeral(v131)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v126, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v113, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v137, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo__24emb_5fVar, &[v139, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v138, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(v143)) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v142, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v136, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v135, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v72, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v55, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Bool(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v149, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v54, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v38, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v26, v153) { Ok(v) => v, Err(e) => return Err(e) };
more_159_eo__24str_5freduction_5fpred(s, v17, v154, v16)
}
pub(super) fn more_157_eo__24str_5freduction_5fpred(s: &mut Store, v100: Term, v94: Term, v93: Term, v92: Term, v91: Term, v73: Term, v2: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v101 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(v101)) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v94, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v93, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match parse_int("122") { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(v106)) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v92, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Bool(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v91, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v73, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v116, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__24emb_5fVar, &[v118, v119]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v117, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(v122)) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v121, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v115, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v114, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_158_eo__24str_5freduction_5fpred(s, v127, v126, v113, v2, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_156_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v74: Term, v73: Term, v72: Term, v55: Term, v54: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match parse_int("97") { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(v76)) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo__24emb_5fVar, &[v82, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v81, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(v86)) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v85, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v79, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v78, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v74, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__24emb_5fVar, &[v97, v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v96, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_157_eo__24str_5freduction_5fpred(s, v100, v94, v93, v92, v91, v73, v2, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_155_eo__24str_5freduction_5fpred(s: &mut Store, v47: Term, v49: Term, v46: Term, v45: Term, v40: Term, v39: Term, v2: Term, v38: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v45, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v40, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v39, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v58, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo__24emb_5fVar, &[v64, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v63, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match parse_int("1") { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.literal(Lit::Numeral(v68)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v57, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v56, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_156_eo__24str_5freduction_5fpred(s, v2, v74, v73, v72, v55, v54, v38, v26, v17, v16)
}
pub(super) fn more_154_eo__24str_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v18: Term, v2: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match parse_int("0") { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(v34)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v28, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v27, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::String(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__24emb_5fVar, &[v42, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_155_eo__24str_5freduction_5fpred(s, v47, v49, v46, v45, v40, v39, v2, v38, v26, v17, v16)
}
