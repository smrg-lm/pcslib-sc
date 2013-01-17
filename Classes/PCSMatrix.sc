// pcslib-sc 2011
// Combinatory Matrix

PCSMatrix {
	var <type;
	var <matrix;
	var <vnorm, <hnorm;

	*fromArray { arg arr, type = \fromArray;
		^this.new.initMatrixFromArray(arr, type);
	}

	initMatrixFromArray { arg arr, t;
		matrix = arr.collect({ arg i;
			i.collect({ arg j;
				j.asArray.as(PCS);
			})
		});
		hnorm = matrix.at(0);
		vnorm = matrix.flop.at(0);
		type = t;
	}

	*roman { arg norm;
		^super.new.initRomanMatrix(norm);
	}

	initRomanMatrix { arg hn;
		type = \roman;

		case({ hn.class == PCS }, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		}, { hn.class == Array }, {
			hn = hn.clump(1).collect({ arg i; i.at(0).asArray.as(PCS) });
		});

		hnorm = vnorm = hn;
		matrix = hnorm.size.collect({ arg i;
			hnorm.rotate(i.neg);
		});
	}

	*t1a { arg norm;
		^super.new.initTypeMatrix(norm, nil, \t1a);
	}

	*t1b { arg norm;
		^super.new.initTypeMatrix(norm, nil, \t1b);
	}

	*t2 { arg hnorm, vnorm;
		^super.new.initTypeMatrix(hnorm, vnorm, \t2);
	}

	initTypeMatrix { arg hn, vn, t;
		var auxOp = \copy; // self

		type = t;

		if(hn.class == PCS, {
			hn = hn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});
		if(vn.class == PCS, {
			vn = vn.asArray.clump(1).collect({ arg i; i.as(PCS) });
		});

		hnorm = hn;
		vnorm = vn ? hn;
		if(type == \t1b, { auxOp = \i });

		matrix = vnorm.collect({ arg i;
			hnorm.collect({ arg j;
				(j.asArray + i.perform(auxOp).asArray).as(PCS);
			});
		});
	}

	*fromChain { arg pcsChain, normParts = 2;
		if(normParts < 1, {
			Error("PCSMatrix *fromChain: normParts < 1").throw;
		});
		^super.new.initChainMatrix(pcsChain.asArray.clump(normParts));
	}

	initChainMatrix { arg hn;
		var rowSize = max(hn.size, hn.at(0).size);
		type = \chain;

		matrix = hn.collect({ arg i, j;
			(i ++ PCS[].dup(rowSize - i.size)).rotate(j);
		});
		hnorm = hn.at(0);
		vnorm = matrix.flop.at(0).reject(_.isEmpty);
	}

	*opcy { arg norm, op;
		^super.new.initOpcyMatrix(norm, op, \opcy);
	}

	initOpcyMatrix { arg norm, op, t;
		var transp, size;

		switch(op.asSymbol,
			'T2/A', {
				transp = 2;
				size = 6;
			},
			'T3/9', {
				transp = 3;
				size = 4;
			},
			'T4/8', {
				transp = 4;
				size = 3;
			},
			'T6/TI', {
				transp = 6;
				size = 2;
			},
			{ Error("PCSMatrix invalid op").throw; }
		);

		matrix = [];
		type = (t ++ " " ++ op).asSymbol;
		hnorm = vnorm = norm;

		if(norm.class == PCS, {
			matrix = size.collect({ arg i;
				var ret;
				ret = ([norm] ++ PCS[].dup(size - 1)).rotate(i);
				norm = norm.t(transp);
				ret;
			});
		}, {
			matrix = size.collect({ arg i;
				var ret;
				ret = (norm ++ PCS[].dup(size - norm.size)).rotate(i);
				norm = norm.collect(_.t(transp));
				ret;
			});
		});
	}

	// cm_trans
	performOnMatrix { arg op ...args;
		var arr = matrix.collect({ arg row;
			row.collect(_.perform(op, *args));
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	i { ^this.performOnMatrix(\i); }
	t { arg n = 0; ^this.performOnMatrix(\t, n); }
	m { arg n = 5; ^this.performOnMatrix(\m, n); }

	r90 { arg clockwise = false;
		var arr = Array.fill2D(matrix.at(0).size, matrix.size);

		if(clockwise, {
			matrix.reverseDo({ arg row, i;
				row.do({ arg pcs, j;
					arr[j][i] = pcs.copy;
				});
			});
			^PCSMatrix.fromArray(arr, this.type);
		}, {
			matrix.do({ arg row, i;
				row.reverseDo({ arg pcs, j;
					arr[j][i] = pcs.copy;
				});
			});
			^PCSMatrix.fromArray(arr, this.type);
		});
	}

	rD {
		var size, arr;

		if(matrix.size != matrix.at(0).size, {
			Error("PCSMatrix-rD the matrix must be squared").throw;
		});

		size = matrix.size;
		arr = Array.fill2D(size, size);

		// r90.invY
		size.do({ arg i;
			(size-i).do({ arg j;
				arr[i][j] = matrix[size-1-j][size-1-i];
				arr[size-1-j][size-1-i] = matrix[i][j];
			});
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	invX {
		var arr = matrix.reverse;
		^PCSMatrix.fromArray(arr, this.type);
	}

	invY {
		var arr = matrix.collect({ arg row;
			row.reverse;
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	eRow { arg r1, r2;
		var arr = matrix.deepCopy; // FIXME: copy, copy...
		var aux = arr[r1];
		arr[r1] = arr[r2];
		arr[r2] = aux;
		^PCSMatrix.fromArray(arr, this.type);
	}

	eCol { arg c1, c2;
		var arr = matrix.deepCopy; // FIXME: copy, copy...
		var aux;
		arr = arr.collect({ arg i;
			aux = i[c1];
			i[c1] = i[c2];
			i[c2] = aux;
			i;
		});
		^PCSMatrix.fromArray(arr, this.type);
	}

	//swap
	swap { arg x1, y1, x2, y2, pc; // swap with params in pdpcslib
		pc = pc.asArray.first; // an int or pcs
		if(this.matrix[y1][x1].includes(pc) and:
			this.matrix[y2][x2].includes(pc), {
				this.matrix[y1][x1].remove(pc);
				this.matrix[y2][x2].remove(pc);
				this.matrix[y1][x2].add(pc);
				this.matrix[y2][x1].add(pc);
		});
	}

	prSwapIfDensity { arg x1, y1, x2, y2, pc;
		if(
			// if the pc is in the second pos? *why duplicates if not ck x1y1*
			(this.matrix[y1][x1].includes(pc) and:
				this.matrix[y2][x2].includes(pc))
			and:
			// if the density is lower in some sense
			(((this.matrix[y1][x1].size > (this.matrix[y1][x2].size)) and:
				(this.matrix[y2][x2].size > (this.matrix[y2][x1].size)))
				or:
				((this.matrix[y1][x1].size > (this.matrix[y2][x1].size)) and:
					(this.matrix[y2][x2].size > (this.matrix[y1][x2].size))))
			// swap
			, {
				this.matrix[y1][x1].remove(pc);
				this.matrix[y2][x2].remove(pc);
				this.matrix[y1][x2].add(pc);
				this.matrix[y2][x1].add(pc);
		});
	}

	swapping { // swap in pdpcslib *check*
		var rowCant, colCant;

		rowCant = this.matrix.size;
		colCant = this.matrix.at(0).size;

		2.do({ // two passes
			// external route
			rowCant.do({ arg y1;
				colCant.do({ arg x1;
					// for each pc in x1, y1
					this.matrix[y1][x1].asArray.do({ arg pc;
						// internal route
						// from the next to y1 a quantity of times = rowCant-1
						// mod12 wraps without reach y1
						((y1+1)..((y1+1) + (rowCant-1))).do({ arg y2;
							y2 = y2 mod: rowCant;
							((x1+1)..((x1+1) + (colCant-1))).do({ arg x2;
								x2 = x2 mod: colCant;
								this.prSwapIfDensity(x1, y1, x2, y2, pc);
							});
						});
					});
				})
			});
		});
	}

	swapStep { // swap1 in pdpcslib
	}

	// cm_ana
	//frag
	//spar
	hist {
		var pfa = Array.fill(12, 0);
		matrix.do({ arg row;
			row.do({ arg pcs;
				pcs.do({ arg i; pfa[i] = pfa[i] + 1 });
			});
		});
		^pfa;
	}

	// cm_2pcs
	pcsAtPos { arg x, y;
		^this.matrix[y][x];
	}

	pcsAtRow { arg n;
		var ret = PCS[];
		this.matrix[n].do({ arg i; ret = ret union: i });
		^ret;
	}

	pcsAtCol { arg n;
		var ret = PCS[];
		this.matrix.do({ arg i; ret = ret union: i[n] });
		^ret;
	}

	pcsAtAll {
		var ret = PCS[];
		this.matrix.flat.do({ arg i; ret = ret union: i });
		^ret;
	}

	printOn { arg stream;
		var maxColSize, strSize;

		// format may be removed
		maxColSize = [];
		matrix.at(0).size.do({ arg i;
			maxColSize = maxColSize.add(0);
			matrix.slice(nil, i).do({ arg obj;
				strSize = obj.asString.size;
				if(strSize > maxColSize[i], {
					maxColSize[i] = strSize;
				});
			});
		});

		if (stream.atLimit) { ^this };
		stream << this.class.name << "[" ;
		matrix.do({ arg row, i;
			if(stream.atLimit, { ^this });
			if(i != 0, { stream.comma });
			stream << "\n";
			stream.space;
			stream << "[ ";
			row.do({ arg obj, j;
				if(stream.atLimit) { ^this };
				obj = obj.asString;
				if(j < (row.size - 1), {
					obj = obj ++ ", ";
					obj = obj.padRight(maxColSize[j] + 2);
				}, {
					obj = obj.padRight(maxColSize[j]);
				});
				obj.printOn(stream);
			});
			stream << " ]";
		});
		stream << "\n";
		stream << "]" ;
	}

	asciiPlot { arg stream, lines = true;
		var maxColSize, strSize;
		var strMatrix;
		var hline;

		stream = stream ? Post;
		maxColSize = [];
		strMatrix = [];

		matrix.at(0).size.do({ arg i;
			maxColSize = maxColSize.add(0);
			strMatrix = strMatrix.add([]);
			matrix.slice(nil, i).do({ arg obj;
				obj = obj
					.asArray
					.replace(10, "A")
					.replace(11, "B")
					.join;
				strSize = obj.size;
				if(strSize > maxColSize[i], {
					maxColSize[i] = strSize;
				});
				strMatrix[i] = strMatrix[i].add(obj);
			});
		});

		if(lines, {
			hline = "+";
			maxColSize.do({ arg n;
				hline = hline ++  "".padRight(n + 2, "-") ++ "+";
			});

			stream << hline;
			stream << "\n";
			strMatrix.flop.do({ arg row, i;
				stream << "|";
				row.do({ arg str, j;
					str = str.padRight(maxColSize[j]);
					str = " " ++ str ++ " |";
					str.printOn(stream);
				});
				stream << "\n";
				stream << hline;
				stream << "\n";
			});
		}, {
			strMatrix.flop.do({ arg row, i;
				row.do({ arg str, j;
					if(str.isEmpty, { str = "." });
					str = str.padRight(maxColSize[j] + 1);
					str.printOn(stream);
				});
				stream << "\n";
			});
		});
	}
}

