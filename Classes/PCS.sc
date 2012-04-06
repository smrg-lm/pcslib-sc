// pcslib-sc 2011
// Pitch Class Set

PCS : OrderedIdentitySet {
	*new { arg n = 2;
		// [] calls new with an Integer, default n MUST be an integer.
		if(n.isInteger, {
			^super.new(n);
		}, {
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
	mi { this.m.i } // shortcut, complete theory

	status {
		var pf, no, t;

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

		if( (self.perform(checkMethod, nexus) or: { self.perform(checkMethod, comp) })
			or: (nexus.perform(checkMethod, self) or: { comp.perform(checkMethod, self) }), {
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

		res = res - res.first % 12; // mod needed for negs.
		resInv = resInv - resInv.first % 12;

		res = PCS.lexMin(res, resInv);
		^res.as(PCS);
	}

	normalOrder {
		var res, rotation, rotDiff, min = 12, auxMin = 12;

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
	*transposition { arg arr, n; ^(arr.asArray + n mod: 12) }
	*multiplication { arg arr, n; ^(arr.asArray * n mod: 12) }

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
			^nil
		});

		^PCS.prLexComb(nset, k, kcomb, last);
	}

	// all variations of k elements
	variations { arg k = 2;
		var nset = this.asArray.copy;
		var n = nset.size;
		var kcomb, last;
		var ret = [];

		if(nset.isEmpty or: { n < k }, {
			^nil
		});

		last = [0] ++ Array.series(k - 1, n - (k - 1));
		n.do({
			kcomb = Array.series(k);
			ret = ret ++ PCS.prLexComb(nset, k, kcomb, last);
			nset = nset.rotate(-1);
		});

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

	binpart { arg a, b, variations = false;
		var ret, sortOp;

		if(a.isNil or: { b.isNil }, {
			a = (this.size/2).floor;
			b = (this.size/2).ceil;
		});
		if(this.size > 8, {
			error("PCS: cardinal number > 8 are not supported for binpart");
			^nil;
		});
		if(a + b != this.size, {
			error("PCS: binpart arguments sum must be equal to this.size");
			^nil;
		});

		ret = this.multiVarpart([a, b]);
		if(variations.not, {
			ret = ret.collectAs({ arg i; i.asSet }, Set); // ...fix
			ret = ret.collectAs({ arg i; i.asArray }, Array); // ...fix
		});

		// sort
		if(a > b, { sortOp = '>' }, { sortOp = '<' });
		ret = ret.collect({ arg i;
			i.sort({ arg x, y;
				x.size.perform(sortOp, y.size);
			})
		});

		^ret;
	}

	// private, by now
	multiVarpart { arg arr;
		var parts, diff, ret = [], subs = [];

		if(arr.notEmpty, {
			parts = this.subsets(arr.at(0));
			parts.do({ arg part;
				subs = multiVarpart(difference(this, part), arr[1..]);
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
			error("PCSs of cardinal number > 8 are not supported for partitions");
			^nil;
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

	*numberOfSubsets { arg m, n = 12;
		^(n.factorial / (m.factorial * (n - m).factorial))
	}

	numberOfSubsets { arg m;
		^PCS.numberOfSubsets(m, this.size);
	}

	*numberOfPartitions { arg m, n = 12;
		// bell number
	}

	numberOfPartitions { arg m;
		^PCS.numberOfPartitions(m, this.size);
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
}

