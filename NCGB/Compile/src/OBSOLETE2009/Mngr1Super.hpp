// MngrSuper.h

#ifndef INCLUDED_MNGRSUPER_H
#define INCLUDED_MNGRSUPER_H

#include "MngrChoice.hpp"
#ifdef USE_MANAGER_ONE_CHOICE
#include "load_flags.hpp"
#include "EditChoices.hpp"
#ifdef WANT_MNGRSUPER
#ifndef INCLUDED_MNGRSTART_H
#include "MngrStart.hpp"
#endif
#ifndef INCLUDED_MORAWORKHORSE_H
#include "MoraWorkHorse.hpp"
#endif
#ifndef INCLUDED_UNIFIERBIN_H
#include "UnifierBin.hpp"
#endif
#ifndef INCLUDED_GBMATCH_H
#include "GBMatch.hpp"
#endif

class MngrSuper : public MngrStart {
  MngrSuper(const MngrSuper &);
    // not implemented
  void operator=(const MngrSuper &);
    // not implemented
public:
  MngrSuper();
  ~MngrSuper();

  void RegisterStartingRelations(int srn);

  // VIRTUAL FUNCTIONS
  virtual const FactBase & factbase() const;
  virtual const list<Polynomial> & startingRelations() const;
  virtual const FactControl & GetFactBase() const;
  virtual FactControl & TheFactBase();
  virtual void reorder(bool n) const;
  virtual void run();
  virtual void run(Polynomial &);
  virtual void continueRun();
  virtual void ForceCleanUpBasis(int iter);
  virtual const GroebnerRule & rule(int n) const;
  virtual int lowvalue() const;
  virtual int numberOfFacts() const;
  virtual pair<int*,int> idsForPartialGBRules() const;
#if 0
  virtual pair<SPIID *,int> reductionsUsed(int) const;
#endif
  virtual int leftIDForSpolynomial(int) const;
  virtual int rightIDForSpolynomial(int) const;
  virtual list<Polynomial> partialBasis() const;
  virtual Polynomial partialBasis(int n) const;
  virtual void partialBasis(int n,Polynomial & aPolynomial) const;
  virtual int iterationNumber(int) const;
  virtual void debug() const;
  int factControlNumber() const {
    return _fcn;
  };
private:
  int _srn;
  int _fcn;
  UnifierBin * _bin;
  MoraWorkHorse * _workHorse;
  bool avoidTheSPolynomial(int first,int second) const;
  bool avoidTheMatchQ(int,int, const Match & ) const;
  void OneStep(int iterationNumber);
  void OneStepNoPrep(int iterationNumber);
  void ManySteps(bool continueQ);
  void cleanIfNecessary(int iterationNumber) {
    if(_cleanFlag) _workHorse->CleanUpBasis(iterationNumber);
  };
  bool d_inCleanUpBasis;
  bool d_tipReduction;
  Reduction * _currentRules;
  int _step;
  mutable list<Polynomial> _startingRelationsHolder;
};
#endif
#endif
#endif
