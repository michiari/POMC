pA() {
  pB();
}

pB() {
  pC();
}

pC() {
  if {
    throw;
  } else {
    pC();
  }
}
