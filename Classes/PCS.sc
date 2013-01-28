// pcslib-sc 2011
// Pitch Class Set

PCS : OrderedIdentitySet {
	*new { arg n = 2;
		// [] calls new with an Integer, default n MUST be an integer.
		if(n.isInteger, {
			^super.new(n);
		}, {
			if(n.class === Array and: { n.class !== String }) {
				^n.as(PCS);
			};
			^super.newFrom(SCTable.pfOf(n));
		});
	}

	name { ^SCTable.nameOf(this) }
	pf { ^this.primeForm }
	mmi { ^SCTable.entryOf(this).at(2) }
	z { ^SCTable.entryOf(this).at(3) }
	icv { ^SCTable.entryOf(this).at(4) }
	iv { ^SCTable.entryOf(this).at(5) }
	cint1 { ^SCTable.entryOf(this).at(6) }

	i { ^this.inversion }
	t { arg n = 0; ^this.transposition(n) }
	m { arg n = 5; ^this.multiplication(n) }
	mi { ^this.multiplication(7) }

	status {
		var pf, no, t;

		if(this.isEmpty, { ^[0, false] });

		pf = this.pf;
		no = this.normalOrder;
		t = no.asArray.first;

		if(pf == no.t(t.neg), {
			^[t, false];
		}, {
			no = this.i.normalOrder;
			t = no.asArray.first;
			^[t, true];
		});
	}

	postStatus {
		var st = this.status;

		if(st.at(1), {
			"T(%)I".format(st.at(0)).postln;
		}, {
			"T(%)".format(st.at(0)).postln;
		});
	}

	// returns [[Tn, I], ...] status in relation to other pcs of the same sc
	relations { arg that;
		var ret = [];

		if(this.name != that.name, {
			Error("PCSs must be of the same SC for relation").throw;
		});

		if(this.isEmpty, { ^[0, false] });

		12.do({ arg i;
			if(this.t(i) == that, {
				ret = ret.add([i, false]);
			});
			if(this.t(i).i == that, {
				ret = ret.add([i, true]);
			});
		});
		^ret;
	}

	complement {
		^PCS('12-1').removeAll(this);
	}

	// Check if SC relationships needs to check i and t (in all abstract relationships)
	scComplement {
		var ret = PCS('12-1').removeAll(this.pf);

		if(ret.notEmpty, {
			^ret.pf;
		}, {
			^ret;
		});
	}

	prKKHPreconditions { arg nexus, comp;
		if(this.size < 3 or: { nexus.size < 3 }
			or: { this.size > 10 } or: { nexus.size > 10 }, {
				^false
		});
		if(this.size == nexus.size or: { this.size == comp.size }, {
			^false
		});
		^true;
	}

	prKKHSetup { arg other, type;
		var self, nexus, comp, checkMethod;

		switch( type,
			'literal', {
				self = this;
				nexus = other;
				comp = other.complement;
				checkMethod = 'includesAll';
			},
			'abstract', {
				self = this.pf;
				nexus = other.pf;
				comp = other.scComplement;
				// FIX, scIsSubsetOf calls pf again,
				// self and nexus may be not necessary.
				checkMethod = 'scIsSubsetOf';
			}
		);

		^[self, nexus, comp, checkMethod];
	}

	k { arg other, type = 'abstract';
		var self, nexus, comp, checkMethod;

		#self, nexus, comp, checkMethod = prKKHSetup(this, other, type);
		if(prKKHPreconditions(this, nexus, comp).not, { ^false });

		if( (self.perform(checkMethod, nexus) or: { nexus.perform(checkMethod, self) })
			or: (self.perform(checkMethod, comp) or: { comp.perform(checkMethod, self) }), {
			^true
		}, {
			^false
		});
	}

	kh { arg other, type = 'abstract';
		var self, nexus, comp, checkMethod;

		#self, nexus, comp, checkMethod = prKKHSetup(this, other, type);
		if(prKKHPreconditions(this, nexus, comp).not, { ^false });

		if( (self.perform(checkMethod, nexus) or: { nexus.perform(checkMethod, self) })
			and: (self.perform(checkMethod, comp) or: { comp.perform(checkMethod, self) }), {
			^true
		}, {
			^false
		});
	}

	primeForm {
		var res, resInv;

		if(this.isEmpty, { ^PCS[] });

		res = this.normalOrder.asArray; // makes mod 12.
		resInv = this.i.normalOrder.asArray;

		res = res - res.first % 12; // mod needed for negs, compiler dependent!
		resInv = resInv - resInv.first % 12;

		res = PCS.lexMin(res, resInv);
		^res.as(PCS);
	}

	normalOrder {
		var res, rotation, rotDiff, min = 12, auxMin = 12;

		if(this.isEmpty, { ^PCS[] });

		// 1
		rotation = this.asArray.sort;

		// 2 y 3
		min = min(min, rotation.last - rotation.first);
		res = rotation;

		(rotation.size - 1).do({ arg i;
			rotation = rotation.rotate(-1);
			rotation = rotation ++ (rotation.pop + 12);
			rotDiff = rotation.last - rotation.first;
			auxMin = min(min, rotDiff);
			if(auxMin < min, {
				min = auxMin;
				res = rotation;
			}, {
				if(rotDiff == min, {
					res = PCS.lexMin(res, rotation);
				});
			});
		});

		^res.as(PCS);
	}

	*lexMin { arg arr1, arr2;
			var pos = 0, notBreak = true;
			var a, b, ret;

			ret = arr1;

			while({pos < (arr1.size - 1) and: notBreak}, {
				a = arr1.at(pos + 1) - arr1.at(pos);
				b = arr2.at(pos + 1) - arr2.at(pos);

				if(b < a, {
					ret = arr2;
					notBreak = false;
				}, {
					if(a < b, {
						notBreak = false;
					});
				});

				pos = pos + 1;
			});
			^ret;
	}

	cardinal { ^this.size; }
	ordinal { ^this.name.asString.split($-).at(1).asInteger; }
	inversion { ^(12 - this.asArray mod: 12).as(PCS) }
	transposition { arg n = 0; ^(this.asArray + n mod: 12).as(PCS) }
	multiplication { arg n = 1; ^(this.asArray * n mod: 12).as(PCS) }

	*inversion { arg arr; ^(12 - arr.asArray mod: 12) }
	*transposition { arg arr, n = 0; ^(arr.asArray + n mod: 12) }
	*multiplication { arg arr, n = 1; ^(arr.asArray * n mod: 12) }

	powerset {
		var result = this.asArray.powerset;
		^result.collect({ arg item; item.as(PCS) });
	}

	// all subsets of k elements
	subsets { arg k = 2;
		var nset = this.asArray;
		var n = nset.size;
		var kcomb = Array.series(k);
		var last = Array.series(k, n - k);

		if(nset.isEmpty or: { n < k }, {
			^[]
		});

		^PCS.prLexComb(nset, k, kcomb, last);
	}

	permute { arg nthPermutation;
		^this.asArray.permute(nthPermutation).as(PCS);
	}

	// permutations of subsets of k elements
	// is better to calculate the subsets and choose a permutation
	// removable method
	vary { arg k = 2, nthPermutation = 0;
		var nset = this.asArray;
		var n = nset.size;
		var kcomb, last;
		var ret = [];

		if(nset.isEmpty or: { n < k }, {
			^[]
		});

		last = [0] ++ Array.series(k - 1, n - (k - 1));
		kcomb = Array.series(k);
		ret = PCS.prLexComb(nset, k, kcomb, last);
		ret = ret.collect({ arg i; i.permute(nthPermutation) });

		^ret;
	}

	// private, lexicographic order subset generator
	*prLexComb { arg nset, k, kcomb, last;
		// based on fxt library
		var n = nset.size;
		var ret = Array.new;
		var j, z;

		ret = ret.add(kcomb.collect({ arg i; nset[i] }).as(PCS));
		while({ kcomb != last }, {
			j = k - 1;
			if(kcomb[j] < (n - 1), {
				kcomb[j] = kcomb[j] + 1;
			}, {
				while({ 1 == (kcomb[j] - kcomb[j - 1]) }, { j = j - 1 });
				z = kcomb[j - 1] + 1;
				kcomb[j - 1] = z;
				while({ j < k }, {
					kcomb[j] = z = z + 1;
					j = j + 1;
				});
			});
			ret = ret.add(kcomb.collect({ arg i; nset[i] }).as(PCS));
		});
		^ret;
	}

	// CHECK variations
	binpart { arg ab, variations = false;
		var ret, sortOp, ite;

		if(this.size > 8, {
			Error("PCS: cardinal number > 8 are not supported for binpart").throw;
		});
		if(ab.notNil, {
			if(ab.size != 2, {
				Error("PCS: binpart ab arg size must be 2").throw;
			});
			if(ab.sum != this.size, {
				Error("PCS: binpart ab arg sum must be equal to size").throw;
			});

			ret = this.varpart([ab.at(0), ab.at(1)]);
			if(ab.at(0) > ab.at(1), { sortOp = '>' }, { sortOp = '<' });
		}, {
			ite = (1..(this.size.div(2)));
			ret = ite.collect({ arg i;
				this.varpart([i, this.size - i]);
			}).flatten;
			sortOp = '<';
		});

		if(variations.not, {
			ret = ret.collectAs({ arg i; i.asSet }, Set); // ...fix
			ret = ret.collectAs({ arg i; i.asArray }, Array); // ...fix
			// and doesn't gives the same order in different excecutions
		});
		ret = ret.collect({ arg i;
			i.sort({ arg x, y;
				x.size.perform(sortOp, y.size);
			})
		});

		^ret;
	}

	// private, by now CHECK arr numbers
	varpart { arg arr;
		var parts, diff, ret = [], subs = [];

		if(arr.notEmpty, {
			parts = this.subsets(arr.at(0));
			parts.do({ arg part;
				subs = varpart(difference(this, part), arr[1..]);
				if(subs.notEmpty, {
					subs = subs.collect({ arg i;
						([part] ++ [i]).flat;
					});
					ret = ret ++ subs;
				}, {
					ret = ret ++ [part];
				});
			});
		});
		^ret;
	}

	partitions {
		var ret = Ref.new([]);
		var arr = this.asArray;
		if(arr.size > 8, {
			Error("PCS: pitch class sets of cardinal > 8 are not supported for partitions").throw;
		});
		PCS.prPartitions(arr, arr.at(0).asArray, 0, ret);
		^ret.value;
	}

	// private
	*prPartitions { arg arr, x, level, ret;
		var auxRet, n;

		level = level + 1;
		if(level < arr.size, {
			n = arr.at(level).asArray;

			if(x.containsSeqColl.not, {
				x = x.clump(1)
			});

			x.size.do({ arg i;
				var aux = x.copy;
				aux[i] = aux[i] ++ n;
				auxRet = auxRet.add(aux);
			});
			auxRet = auxRet.add(x.copy.add(n));

			auxRet.do({ arg i;
				PCS.prPartitions(arr, i, level, ret);
			});

			if(level == (arr.size - 1), {
				auxRet = auxRet.collect({ arg i;
					i = i.collect({ arg j; j.as(PCS) });
				});
				ret.value = ret.value ++ auxRet;
			});
		});
	}

	// relations
	*prCheckEqualCardinality { arg a, b, m;
		if(a.cardinal != b.cardinal, {
			Error(
				"PCS: pitch class sets must be of the same cardinality for % comparison".format(m)
			).throw;
		});
	}

	rp { arg that;
		var subA, subB;
		var compcs = [], comsc = [];
		var rp = false, strong = false;

		PCS.prCheckEqualCardinality(this, that, "rp");
		subA = this.subsets(this.cardinal - 1);
		subB = that.subsets(that.cardinal - 1);

		subA.do({ arg i;
			subB.do({ arg j;
				if(i == j, {
					rp = true;
					strong = true;
					compcs = compcs.add(i);
				}, {
					if(i.pf == j.pf, {
						rp = true;
						comsc = comsc.add([i, j]);
					});
				})
			});
		});
		^[rp, strong, compcs, comsc]
	}

	r0 { arg that;
		var icvdif;

		PCS.prCheckEqualCardinality(this, that, "r0");
		icvdif = (this.icv - that.icv)[1..];

		icvdif.do({ arg i; if(i == 0, { ^false }) });
		^true;
	}

	r1 { arg that;
		var icvdif, count = 0, inter = [];

		PCS.prCheckEqualCardinality(this, that, "r1");
		icvdif = (this.icv - that.icv)[1..];

		icvdif.do({ arg i;
			if(i == 0, {
				count = count + 1;
			}, {
				inter = inter.add(i);
			});
		});
		^if(count == 4 and: { inter.sum == 0 }, { true }, { false });
	}

	r2 { arg that;
		var icvdif, count = 0;

		PCS.prCheckEqualCardinality(this, that, "r2");
		icvdif = (this.icv - that.icv)[1..];

		icvdif.do({ arg i; if(i == 0, { count = count + 1 }) });
		^if(count >= 4, { true }, { false });
	}

	sim { arg that;
		var icvA, icvB;
		var maxsim, minsim, ret;

		icvA = this.icv[1..];
		icvB = that.icv[1..];
		ret = icvA.absdif(icvB).sum;
		maxsim = icvA.sum + icvB.sum;
		minsim = icvA.sum absdif: icvB.sum;

		^[ret, maxsim, minsim];
	}

	asim { arg that;
		var icvA, icvB;
		var res, nfac;

		icvA = this.icv[1..];
		icvB = that.icv[1..];
		res = icvA.absdif(icvB).sum;
		nfac = (icvA + icvB).sum;

		^res/nfac;
	}

	icvsim { arg that;
		var icvA, icvB;
		var idv, mean;
		var ret;

		icvA = this.icv[1..];
		icvB = that.icv[1..];
		idv = icvB - icvA;
		mean = idv.sum / 6;
		ret = (idv - mean).pow(2).sum;
		ret = (ret / 6).sqrt;

		^ret;
	}

	// double check titn/invariants
	tMatrix { arg that;
		var arr, ret;

		arr = that.asArray;
		ret = this.i.asArray.dup(1).flop;
		ret = ret.collect({ arg i; arr+i%12 });

		^ret;
	}

	itMatrix { arg that;
		var arr, ret;

		arr = that.asArray;
		ret = this.asArray.dup(1).flop;
		ret = ret.collect({ arg i; arr+i%12 });

		^ret;
	}

	invariants { arg that, subset, op = \t;
		var arr, aux, posi, ret = [];

		if(subset.isSubsetOf(that), {
			posi = subset.asArray.collect({ arg pc;
				that.asArray.indexOf(pc);
			});
		}, {
			Error("subset must be a subset of that").throw;
		});
		switch( op,
			\t, { arr = this.tMatrix(that); },
			\it, { arr = this.itMatrix(that); },
			{ Error("op must be \t or \it").throw }
		);
		aux = Array.fill(12, 0).dup(subset.size);

		arr.do({ arg row;
			posi.do({ arg pos, j;
				aux[j][row.at(pos)] = 1;
			});
		});
		aux.sum.do({ arg i, j;
			if(i == subset.size, { ret = ret.add(j) });
		});

		^ret;
	}

	*numberOfSubsets { arg k, n = 12;
		^n.factorial / (k.factorial * (n - k).factorial)
	}

	numberOfSubsets { arg k;
		^PCS.numberOfSubsets(k, this.size);
	}

	*numberOfPermutations { arg n = 12;
		^n.factorial;
	}

	numberOfPermutations {
		^PCS.numberOfPermutations(this.size);
	}

	*numberOfVariations { arg k, n = 12;
		^n.factorial / (n - k).factorial;
	}

	numberOfVariations { arg k;
		^PCS.numberOfVariations(k, this.size);
	}

	// number of partitions
	// there is a special algorithm
	*bellNumber { arg n = 12;
		var ret = 0;
		(0..n).do({ arg k;
			ret = ret + PCS.stirlingNumber(k, n);
		});
		^ret;
	}

	bellNumber {
		^PCS.bellNumber(this.size);
	}

	// for number of binary, etc. partitions
	*stirlingNumber { arg k, n = 12;
		var ret = 0;
		if(k == n) { ^1 };
		if(k == 0) { ^0 };
		if(k > n) { "k must be <= n, k = %, n = %".format(k, n).warn; ^nil };
		(1..k).do({ arg j;
			ret = ret  + (-1.pow(k-j) * (j.pow(n-1) /
			((j - 1).factorial * (k - j).factorial)));
		});
		^ret.round.asInteger;
	}

	stirlingNumber { arg k;
		^PCS.stirlingNumber(k, this.size);
	}

	scIsSubsetOf { arg that;
		//^that.pf.includesAll(this.pf) // has no sense is = to subsetOf
		var subSets = that.subsets(this.size);
		var thisPf = this.pf;
		subSets.do({ arg pcs;
			if(pcs.pf.includesAll(thisPf), { ^true });
		});
		^false;
	}
	//scSect { }
	//scUnion { }
	//scDifference { }
	//scSymmetricDifference { }

	pcsHash {
		// modified Collection:hash
		var hash = 0;
		this.do { | item |
			hash = hash bitXor: item.hash;
		};
		^hash
	}

	// overwirte //
	add { arg item; super.add(item mod: 12) }

	//addAll { }
	//species { ^this.class }
	//copy { ^this.deepCopy } // SUPERCLASS FIXED 3.5

	embedInStream { arg inval;
		this.do({ arg pc; inval = pc.yield })
		.isEmpty.if({ inval = nil.yield });
	}

	asStream {
		^Routine({ arg inval; this.embedInStream(inval) })
	}
}
