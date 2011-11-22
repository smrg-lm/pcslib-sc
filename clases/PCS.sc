// pcslib-sc 2011
// Pitch Class Set

/*
HACER:
- kh, scSetOperations, etc.
- agregar "status" (con respecto a la forma prima Tn I, ver pcs_2txt)
*/

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
	
	//np { ^this.normalPosition } // no sirve si contiene repeticones.
	i { ^this.inversion }
	t { arg n = 0; ^this.transposition(n) }
	m { arg n = 5; ^this.multiplication(n) }
	
	primeForm {
		var res;
		
		// 1, 2 y 3
		res = this.normalPosition.asArray;
		
		// 4
		res = res - res.first;
		
		if(res.size > 2 and: {
				(res.at(1) - res.at(0))
				>
				(res.wrapAt(-1) - res.wrapAt(-2))
			}) {
			res = res.reverse; // retro
			res = PCS.inversion(res); // inv
			res = res - res.first % 12;
		};
		
		^res.as(PCS);
	}
	
	normalPosition {
		var res, rotation, min = 12, auxMin = 12;
		
		// 1
		res = this.asArray.sort;
		
		// 2 y 3
		min = min(min, res.last - res.first);
		rotation = res;
		(res.size - 1).do({ arg i;
			rotation = rotation.rotate(-1);
			rotation = rotation ++ (rotation.pop + 12);
			auxMin = min(min, rotation.last - rotation.first);
			if(auxMin < min, {
				min = auxMin;
				res = rotation;
			});
		});
		
		^res.as(PCS);
	}
	
	cardinal { ^this.size; }
	inversion { ^(12 - this.asArray mod: 12).as(PCS) }
	transposition { arg n = 0; ^(this.asArray + n mod: 12).as(PCS) }
	multiplication { arg n = 1; ^(this.asArray * n mod: 12).as(PCS) }
	
	// arrays (mŽtodos auxiliares, private
	// borrar? -ver m‡s arriba y los mŽtodos pr m‡s abajo-)
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
		var ret;
		
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
		^ret;
	}
	
	// private, por ahora
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
		// nœmero campana.
	}
	
	numberOfPartitions { arg m;
		^PCS.numberOfPartitions(m, this.size);
	}
	
	scIsSubsetOf { arg that;
		//^that.pf.includesAll(this.pf) // no tiene sentido es lo mismo que subsetOf
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
	//copy { ^this.deepCopy } // SUPERCLASS FIXED
}
