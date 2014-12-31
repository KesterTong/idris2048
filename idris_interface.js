var IdrisInterface = function(element, grid_size) {
	this.callbacks_ = [];
	this.events_ = [];
	this.element_ = element;

	/**
	 * Array of grid cells, arranged in row major format
	 */
	this.cells_ = this.get_cells_(grid_size);

	var that = this;
	element.addEventListener('keydown', function(e) {that.on_keydown_(e)});
}

IdrisInterface.prototype.get_cells_ = function(grid_size) {
	var cells = [];
	for (var i = 0; i < grid_size; i++) {
		for (var j = 0; j < grid_size; j++) {
			cells.push(document.getElementById("" + i + "" + j));
		}
	}
	return cells;
}

IdrisInterface.prototype.on_keydown_ = function(e) {
	if (this.callbacks_.length > 0) {
		this.callbacks_.shift()(e['keyCode']);
	} else {
		this.events_.push(e);
	}
}

IdrisInterface.prototype.get_next_event = function(callback) {
	if (this.events_.length > 0) {
		var e = this.events_.shift();
		callback(this.events_.shift());	
	} else {
		this.callbacks_.push(callback);
	}	
}

IdrisInterface.prototype.show = function(str) {
	if (str.length != this.cells_.length) {
		console.error('str had different length to the number of cells');
		return;
	}
	for (var i = 0; i < str.length; i++) {
		var cell_value = str.charCodeAt(i)
		var cell_html = cell_value == 0 ? '' : Math.pow(2, cell_value);
		this.cells_[i].innerHTML = cell_html;
	}
}

var idris_interface = new IdrisInterface(document.getElementById('game-area'), 4);
